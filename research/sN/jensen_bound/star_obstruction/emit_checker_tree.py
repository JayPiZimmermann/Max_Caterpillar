#!/usr/bin/env python3
"""Emit bounded kernel-checked ternary-tree certificate modules (Lean 4.4).

The JSON is untrusted input. This producer validates its schema and exact
rational identities independently, then emits ordinary `decide` checks.
Start with --smoke: one complete three-branch subtree containing a nonzero
zero-span identity. The actual star-expression semantic bridge is separate.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import re
import math
from typing import Union

ROOT = Path(__file__).resolve().parents[4]
INPUT = Path(__file__).with_name("exact_tree_candidate.json")
OUT = ROOT / "MaxCaterpillar/Frontier/StarCertificate/Checker/Generated"
SIGNS = {-1: ".neg", 0: ".zero", 1: ".pos"}
M, N, K = 15, 4, 80


@dataclass(frozen=True)
class Solved:
    index: int
    pattern: tuple[int, ...]
    coefficients: tuple[tuple[Fraction, ...], ...]
    multipliers: tuple[tuple[Fraction, ...], ...]


@dataclass(frozen=True)
class Impossible:
    index: int
    prefix: tuple[int, ...]
    weights: tuple[Fraction, ...]


@dataclass(frozen=True)
class Branch:
    depth: int
    children: tuple["Node", "Node", "Node"]


Node = Union[Solved, Impossible, Branch]


class Lean:
    """One renderer for identifiers, literals, vectors, and sparse functions."""
    keywords = {"def", "theorem", "match", "with", "where", "by", "do", "end", "prefix", "infix", "syntax", "notation"}

    @classmethod
    def ident(cls, text: str) -> str:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", text) or text in cls.keywords:
            raise ValueError(f"Invalid generated identifier: {text}")
        return text

    @staticmethod
    def rat(q: Fraction) -> str:
        if q.denominator == 1:
            return f"({q.numerator} : ℚ)"
        return f"({q.numerator} / {q.denominator} : ℚ)"

    @staticmethod
    def vector(items: list[str]) -> str:
        if not items:
            raise ValueError("Empty vectors require a separately typed Fin 0 function")
        return "![" + ", ".join(items) + "]"

    @classmethod
    def rats(cls, row: tuple[Fraction, ...]) -> str:
        return "0" if not any(row) else cls.vector([cls.rat(q) for q in row])

    @classmethod
    def balanced_table(cls, rows, render, lo=0):
        if not rows:
            raise ValueError("Empty lookup table")
        if all(row == rows[0] for row in rows):
            return render(rows[0])
        middle = len(rows) // 2
        left = cls.balanced_table(rows[:middle], render, lo)
        right = cls.balanced_table(rows[middle:], render, lo + middle)
        return f"if t.val < {lo + middle} then ({left}) else ({right})"

    @classmethod
    def matrix(cls, rows: tuple[tuple[Fraction, ...], ...], width: int) -> str:
        body = cls.balanced_table(rows, cls.rats)
        return "0" if body == "0" else ("fun t => " if "t.val" in body else "fun _ => ") + body

    @staticmethod
    def integer(q: Fraction) -> str:
        if q.denominator != 1:
            raise ValueError("Nonintegral literal in integer certificate")
        return f"({q.numerator} : ℤ)"

    @classmethod
    def integers(cls, row: tuple[Fraction, ...]) -> str:
        return "0" if not any(row) else cls.vector([cls.integer(q) for q in row])

    @classmethod
    def integer_matrix(cls, rows: tuple[tuple[Fraction, ...], ...]) -> str:
        body = cls.balanced_table(rows, cls.integers)
        return "0" if body == "0" else ("fun t => " if "t.val" in body else "fun _ => ") + body

    @classmethod
    def pattern(cls, signs: tuple[int, ...]) -> str:
        return cls.vector([SIGNS[s] for s in signs])

    @classmethod
    def context(cls, prefix: tuple[int, ...]) -> str:
        return cls.vector(["some " + SIGNS[s] for s in prefix] + ["none"] * (M - len(prefix)))


def atomic(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(text, encoding="utf-8")
    os.replace(temporary, path)


def forms() -> list[list[Fraction]]:
    return [[Fraction((mask >> i) & 1) for i in range(N)] for mask in range(1, 16)]


def load(path: Path) -> tuple[Node, dict]:
    data = json.loads(path.read_text())
    if data["form_masks"] != list(range(1, 16)) or len(data["pair_order"]) != K:
        raise ValueError("Unexpected form or target ordering")
    if data["xi_scale"] != 240:
        raise ValueError("Unexpected Xi normalization")
    A = forms()
    solved: list[Solved] = []
    for index, record in enumerate(data["leaves"]):
        pattern = tuple(record["pattern"])
        if len(pattern) != M or any(s not in SIGNS for s in pattern):
            raise ValueError(f"Bad pattern at leaf {index}")
        coeff = tuple(tuple(Fraction(q) for q in row) for row in record["identities"])
        masks = record["lambda_masks"]
        if len(coeff) != K or any(len(row) != N for row in coeff):
            raise ValueError(f"Bad target matrix at leaf {index}")
        weights = []
        for t, short in enumerate(record["multipliers"]):
            if len(short) != len(masks):
                raise ValueError(f"Bad multiplier row at leaf {index}, target {t}")
            row = [Fraction(0)] * M
            for mask, q in zip(masks, short):
                if not 1 <= mask <= M or pattern[mask - 1] != 0:
                    raise ValueError(f"Nonzero-face multiplier at leaf {index}")
                row[mask - 1] = Fraction(q)
            for i in range(N):
                if coeff[t][i] != sum(row[j] * A[j][i] for j in range(M)):
                    raise ValueError(f"Wrong zero-span identity at leaf {index}, target {t}")
            weights.append(tuple(row))
        if len(weights) != K:
            raise ValueError(f"Bad target multiplier count at leaf {index}")
        solved.append(Solved(index, pattern, coeff, tuple(weights)))
    impossible: list[Impossible] = []
    for index, record in enumerate(data["excluded"]):
        prefix = tuple(record["prefix"])
        raw = tuple(Fraction(q) for q in record["weights"])
        if len(raw) != len(prefix) or len(prefix) > M:
            raise ValueError(f"Bad Farkas prefix {index}")
        if any(s not in SIGNS for s in prefix):
            raise ValueError(f"Bad Farkas signs {index}")
        if any(q < 0 for s, q in zip(prefix, raw) if s):
            raise ValueError(f"Negative strict weight {index}")
        if not any(q > 0 for s, q in zip(prefix, raw) if s):
            raise ValueError(f"No strict positive weight {index}")
        for i in range(N):
            if sum(q * (-1 if s == -1 else 1) * A[j][i]
                   for j, (s, q) in enumerate(zip(prefix, raw))) != 0:
                raise ValueError(f"Wrong Farkas identity {index}")
        impossible.append(Impossible(index, prefix, raw + (Fraction(0),) * (M - len(prefix))))

    used_solved, used_impossible = set(), set()

    def node(raw, prefix: tuple[int, ...]) -> Node:
        if raw[0] == "branch":
            if len(raw) != 4 or len(prefix) >= M:
                raise ValueError("Malformed branch")
            children = tuple(node(child, prefix + (s,)) for s, child in zip((-1, 0, 1), raw[1:]))
            return Branch(len(prefix), children)
        if len(raw) != 2:
            raise ValueError("Malformed terminal")
        index = raw[1]
        if raw[0] == "leaf":
            result = solved[index]
            if result.pattern != prefix:
                raise ValueError(f"Tree/solved pattern disagreement {index}")
            used_solved.add(index)
            return result
        if raw[0] == "exclude":
            result = impossible[index]
            if result.prefix != prefix:
                raise ValueError(f"Tree/Farkas prefix disagreement {index}")
            used_impossible.add(index)
            return result
        raise ValueError(f"Unknown node kind {raw[0]}")

    tree = node(data["tree"], ())
    if len(used_solved) != len(solved) or len(used_impossible) != len(impossible):
        raise ValueError("Unreferenced certificate record")
    return tree, data


def smoke(tree: Node) -> tuple[tuple[int, ...], Branch]:
    def seek(node: Node, prefix: tuple[int, ...]):
        if isinstance(node, Branch):
            if node.depth == M - 1 and any(isinstance(c, Solved) and
                    any(any(row) for row in c.coefficients) for c in node.children):
                return prefix, node
            for s, child in zip((-1, 0, 1), node.children):
                found = seek(child, prefix + (s,))
                if found is not None:
                    return found
        return None
    result = seek(tree, ())
    if result is None:
        raise ValueError("No representative nonzero-span smoke subtree")
    return result


def emit_smoke(tree: Node, input_path: Path) -> Path:
    prefix, subtree = smoke(tree)
    for name in ("regionContext", "targets", "tree", "checked", "sound"):
        Lean.ident(name)
    solved = [node for node in subtree.children if isinstance(node, Solved)]
    impossible = [node for node in subtree.children if isinstance(node, Impossible)]
    sha = hashlib.sha256(input_path.read_bytes()).hexdigest()
    header = f'''import MaxCaterpillar.Frontier.StarCertificate.Checker
import MaxCaterpillar.Frontier.StarCertificate.XiSelectors

/-! Generated by emit_checker_tree.py --smoke.
Input: exact_tree_candidate.json SHA256 {sha}
Complete three-way subtree at depth {len(prefix)}; this is a bounded
checker test, not a certificate for the full arrangement or star identity.
-/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000
namespace MaxCaterpillar.Frontier.StarCertificate.Generated.Smoke
open BigOperators

def regionContext : Context 15 := {Lean.context(prefix)}
'''
    declarations = []
    for leaf in solved:
        declarations.append(f"def pattern{leaf.index} : Fin 15 → Sign := {Lean.pattern(leaf.pattern)}")
        declarations.append(f"def coeff{leaf.index} : Fin 80 → RationalForm 4 :=\n  {Lean.matrix(leaf.coefficients, N)}")
        declarations.append(f"def lambda{leaf.index} : Fin 80 → Fin 15 → ℚ :=\n  {Lean.matrix(leaf.multipliers, M)}")
    for leaf in impossible:
        declarations.append(f"def weights{leaf.index} : Fin 15 → ℚ := {Lean.rats(leaf.weights)}")
    target = "0"
    for leaf in reversed(solved):
        target = f"if p = pattern{leaf.index} then coeff{leaf.index} else ({target})"
    declarations.append("def targets (p : Fin 15 → Sign) : Fin 80 → RationalForm 4 :=\n  " + target)
    children = []
    for child in subtree.children:
        if isinstance(child, Solved):
            children.append(f"(.solved lambda{child.index})")
        elif isinstance(child, Impossible):
            children.append(f"(.impossible weights{child.index})")
        else:
            raise ValueError("Smoke subtree unexpectedly contains nested branch")
    declarations.append(f"def tree : CertificateTree 15 80 :=\n  .split 14 {' '.join(children)}")
    footer = '''
theorem checked : tree.check subsetForms targets regionContext = true := by
  with_unfolding_all rfl

theorem sound (x : Fin 4 → ℝ) (hx : Holds subsetForms regionContext x) :
    ∀ t, evalForm (targets (actualSigns subsetForms x) t) x = 0 :=
  tree.valid_sound subsetForms targets regionContext
    ((tree.check_eq_true_iff_valid subsetForms targets regionContext).mp checked) x hx

#print axioms sound
end MaxCaterpillar.Frontier.StarCertificate.Generated.Smoke
'''
    path = OUT / "Smoke.lean"
    atomic(path, header + "\n\n".join(declarations) + "\n" + footer)
    record = {"input_sha256": sha, "producer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), "prefix": prefix,
              "solved_leaf_ids": [x.index for x in solved],
              "excluded_leaf_ids": [x.index for x in impossible],
              "output": str(path.relative_to(ROOT)),
              "output_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
              "command": "python3 research/sN/jensen_bound/star_obstruction/emit_checker_tree.py --smoke"}
    atomic(input_path.with_name("checker_smoke_generation.json"), json.dumps(record, indent=2) + "\n")
    return path


def cleared(row: tuple[Fraction, ...]) -> tuple[int, tuple[Fraction, ...]]:
    denominator = math.lcm(*(q.denominator for q in row))
    return denominator, tuple(q * denominator for q in row)


def emit_integer_smoke(tree: Node, input_path: Path) -> Path:
    prefix, subtree = smoke(tree)
    solved = [node for node in subtree.children if isinstance(node, Solved)]
    impossible = [node for node in subtree.children if isinstance(node, Impossible)]
    sha = hashlib.sha256(input_path.read_bytes()).hexdigest()
    header = f'''import MaxCaterpillar.Frontier.StarCertificate.Checker
import MaxCaterpillar.Frontier.StarCertificate.XiSelectors

/-! Generated by emit_checker_tree.py --integer-smoke.
Input: exact_tree_candidate.json SHA256 {sha}
Integer-cleared complete three-way subtree; bounded arithmetic benchmark.
-/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000
namespace MaxCaterpillar.Frontier.StarCertificate.Generated.IntegerSmoke
open BigOperators

def forms : Fin 15 → Fin 4 → ℤ :=
  {Lean.vector([Lean.integers(tuple(row)) for row in forms()])}

theorem forms_cast : integerForms forms = subsetForms :=
  of_decide_eq_true (by with_unfolding_all rfl)

def regionContext : Context 15 := {Lean.context(prefix)}
'''
    declarations = []
    for leaf in solved:
        dens, rows = zip(*(cleared(row) for row in leaf.multipliers))
        den_term = "(1 : ℤ)"
        for i, den in reversed(list(enumerate(dens))):
            if den != 1:
                den_term = f"if t = {i} then ({den} : ℤ) else ({den_term})"
        declarations.append(f"def pattern{leaf.index} : Fin 15 → Sign := {Lean.pattern(leaf.pattern)}")
        declarations.append(f"def coeff{leaf.index} : Fin 80 → Fin 4 → ℤ :=\n  {Lean.integer_matrix(leaf.coefficients)}")
        declarations.append(f"def den{leaf.index} : Fin 80 → ℤ := fun t => {den_term}")
        declarations.append(f"def lambda{leaf.index} : Fin 80 → Fin 15 → ℤ :=\n  {Lean.integer_matrix(tuple(rows))}")
    for leaf in impossible:
        _, weights = cleared(leaf.weights)
        declarations.append(f"def weights{leaf.index} : Fin 15 → ℤ := {Lean.integers(weights)}")
    target = "0"
    for leaf in reversed(solved):
        target = f"if p = pattern{leaf.index} then coeff{leaf.index} else ({target})"
    declarations.append("def targets (p : Fin 15 → Sign) : Fin 80 → Fin 4 → ℤ :=\n  " + target)
    children = []
    for child in subtree.children:
        if isinstance(child, Solved):
            children.append(f"(.solved den{child.index} lambda{child.index})")
        elif isinstance(child, Impossible):
            children.append(f"(.impossible weights{child.index})")
        else:
            raise ValueError("Integer smoke subtree unexpectedly nested")
    declarations.append(f"def tree : IntegerCertificateTree 15 80 :=\n  .split 14 {' '.join(children)}")
    footer = '''
theorem checked : tree.check forms targets regionContext = true := by
  with_unfolding_all rfl

theorem sound (x : Fin 4 → ℝ) (hx : Holds subsetForms regionContext x) :
    ∀ t, evalForm (fun i => (targets (actualSigns subsetForms x) t i : ℚ)) x = 0 := by
  have hp : Holds (integerForms forms) regionContext x := by rw [forms_cast]; exact hx
  have ht := tree.rational_valid forms targets regionContext
    ((tree.check_eq_true_iff_valid forms targets regionContext).mp checked)
  have he := tree.rational.valid_sound (integerForms forms) (fun s t i => (targets s t i : ℚ))
    regionContext ht x hp
  simpa only [forms_cast] using he

#print axioms sound
end MaxCaterpillar.Frontier.StarCertificate.Generated.IntegerSmoke
'''
    path = OUT / "IntegerSmoke.lean"
    atomic(path, header + "\n\n".join(declarations) + "\n" + footer)
    record = {"input_sha256": sha,
              "producer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "prefix": prefix, "solved_leaf_ids": [x.index for x in solved],
              "excluded_leaf_ids": [x.index for x in impossible],
              "output": str(path.relative_to(ROOT)),
              "output_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
              "command": "python3 research/sN/jensen_bound/star_obstruction/emit_checker_tree.py --integer-smoke"}
    atomic(input_path.with_name("checker_integer_smoke_generation.json"), json.dumps(record, indent=2) + "\n")
    return path


def emit_target_benchmark(tree: Node, input_path: Path) -> Path:
    _, subtree = smoke(tree)
    leaf = next(x for x in subtree.children if isinstance(x, Solved) and any(any(r) for r in x.coefficients))
    sha = hashlib.sha256(input_path.read_bytes()).hexdigest()
    text = f'''import MaxCaterpillar.Frontier.StarCertificate.XiTargets
/-! Generated by emit_checker_tree.py --target-benchmark.
Input SHA256 {sha}; representative solved leaf {leaf.index}.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.TargetBenchmark
def pattern : Fin 15 → Sign := {Lean.pattern(leaf.pattern)}
def expected : Fin 80 → Fin 4 → ℤ := {Lean.integer_matrix(leaf.coefficients)}
theorem direct_match : ∀ t i, starAnovaIntegerCoefficients pattern t i = expected t i :=
  of_decide_eq_true (by with_unfolding_all rfl)
#print axioms direct_match
end MaxCaterpillar.Frontier.StarCertificate.TargetBenchmark
'''
    path = input_path.with_name("TargetBenchmark.lean")
    atomic(path, text)
    return path


@dataclass(frozen=True)
class Chunk:
    index: int
    prefix: tuple[int, ...]
    tree: Branch


def terminals(tree: Node) -> tuple[list[Solved], list[Impossible]]:
    solved, impossible = [], []
    def walk(node: Node) -> None:
        if isinstance(node, Branch):
            for child in node.children:
                walk(child)
        elif isinstance(node, Solved):
            solved.append(node)
        else:
            impossible.append(node)
    walk(tree)
    return solved, impossible


def partition(tree: Node, max_terms: int, max_solved: int):
    chunks = []
    def walk(node: Node, prefix: tuple[int, ...]):
        if not isinstance(node, Branch):
            return node
        solved, impossible = terminals(node)
        if len(solved) <= max_solved and len(solved) + len(impossible) <= max_terms:
            result = Chunk(len(chunks), prefix, node)
            chunks.append(result)
            return result
        return Branch(node.depth, tuple(walk(c, prefix + (s,))
                                       for s, c in zip((-1, 0, 1), node.children)))
    top = walk(tree, ())
    return chunks, top


def integer_data_declarations(tree: Node) -> list[str]:
    solved, impossible = terminals(tree)
    lines = []
    for leaf in solved:
        dens, rows = zip(*(cleared(row) for row in leaf.multipliers))
        den_term = "(1 : ℤ)"
        for i, den in reversed(list(enumerate(dens))):
            if den != 1:
                den_term = f"if t = {i} then ({den} : ℤ) else ({den_term})"
        lines.extend([
            f"def pattern{leaf.index} : Fin 15 → Sign := {Lean.pattern(leaf.pattern)}",
            f"def coeff{leaf.index} : Fin 80 → Fin 4 → ℤ :=\n  {Lean.integer_matrix(leaf.coefficients)}",
            f"def den{leaf.index} : Fin 80 → ℤ := fun t => {den_term}",
            f"def lambda{leaf.index} : Fin 80 → Fin 15 → ℤ :=\n  {Lean.integer_matrix(tuple(rows))}"])
    for leaf in impossible:
        _, weights = cleared(leaf.weights)
        lines.append(f"def weights{leaf.index} : Fin 15 → ℤ := {Lean.integers(weights)}")
    return lines


def tree_term(node: Node) -> str:
    if isinstance(node, Chunk):
        return f"Chunk{node.index:04d}.tree"
    if isinstance(node, Solved):
        return f"(.solved den{node.index} lambda{node.index})"
    if isinstance(node, Impossible):
        return f"(.impossible weights{node.index})"
    return f"(.split {node.depth} " + " ".join(tree_term(c) for c in node.children) + ")"


def agreement_proof(node: Node, context: str, indent: str = "  ") -> list[str]:
    if isinstance(node, Impossible):
        return [indent + "exact True.intro"]
    if isinstance(node, Solved):
        i = node.index
        return [indent + f"change targets (contextSigns ({context})) = C (contextSigns ({context}))",
                indent + f"have hp : contextSigns ({context}) = pattern{i} :=",
                indent + "  of_decide_eq_true (by with_unfolding_all rfl)",
                indent + "rw [hp]",
                indent + f"have hc : targets pattern{i} = coeff{i} := by with_unfolding_all rfl",
                indent + "rw [hc]",
                indent + f"exact h{i}.symm"]
    result = [indent + "refine ⟨?_, ?_, ?_⟩"]
    for sign, child in zip((-1, 0, 1), node.children):
        child_context = f"Function.update ({context}) {node.depth} (some {SIGNS[sign]})"
        child_lines = agreement_proof(child, child_context, indent + "  ")
        result.append(indent + "· " + child_lines[0][len(indent)+2:])
        result.extend(child_lines[1:])
    return result


def emit_chunk(chunk: Chunk, input_sha: str) -> Path:
    solved, _ = terminals(chunk.tree)
    name = Lean.ident(f"Chunk{chunk.index:04d}")
    header = f'''import MaxCaterpillar.Frontier.StarCertificate.Checker
import MaxCaterpillar.Frontier.StarCertificate.XiInteger
/-! Generated by emit_checker_tree.py --chunks; input SHA256 {input_sha}.
Complete bounded subtree at depth {len(chunk.prefix)}. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.Generated.{name}
open BigOperators
def regionContext : Context 15 := {Lean.context(chunk.prefix)}
'''
    lines = integer_data_declarations(chunk.tree)
    target = "0"
    for leaf in reversed(solved):
        target = f"if p = pattern{leaf.index} then coeff{leaf.index} else ({target})"
    lines.append("def targets (p : Fin 15 → Sign) : Fin 80 → Fin 4 → ℤ :=\n  " + target)
    lines.append("def tree : IntegerCertificateTree 15 80 :=\n  " + tree_term(chunk.tree))
    lines.append("theorem checked : tree.check starIntegerSubsetForms targets regionContext = true := by\n  with_unfolding_all rfl")
    binders = "\n".join(f"    (h{leaf.index} : C pattern{leaf.index} = coeff{leaf.index})" for leaf in solved)
    proof = agreement_proof(chunk.tree, "regionContext", "  ")
    lines.append(f'''theorem agreement (C : (Fin 15 → Sign) → Fin 80 → Fin 4 → ℤ)
{binders} : tree.Agrees targets C regionContext := by
''' + "\n".join(proof))
    arguments = " ".join(f"h{leaf.index}" for leaf in solved)
    lines.append(f'''theorem valid (C : (Fin 15 → Sign) → Fin 80 → Fin 4 → ℤ)
{binders} : tree.Valid starIntegerSubsetForms C regionContext :=
  tree.valid_congr starIntegerSubsetForms targets C regionContext
    ((tree.check_eq_true_iff_valid starIntegerSubsetForms targets regionContext).mp checked)
    (agreement C {arguments})''')
    lines.append(f"#print axioms valid\nend MaxCaterpillar.Frontier.StarCertificate.Generated.{name}")
    path = OUT / (name + ".lean")
    atomic(path, header + "\n\n".join(lines) + "\n")
    return path


def direct_valid_proof(node: Node, context: str, indent: str = "  ") -> list[str]:
    if isinstance(node, (Solved, Impossible)):
        i = node.index
        ctx_name = f"solvedContext{i}" if isinstance(node, Solved) else f"excludedContext{i}"
        numeric_name = f"solvedNumeric{i}" if isinstance(node, Solved) else f"excludedNumeric{i}"
        result = [indent + f"have hp : ({context}) = {ctx_name} :=",
                  indent + "  of_decide_eq_true (by with_unfolding_all rfl)",
                  indent + "rw [hp]"]
        if isinstance(node, Impossible):
            return result + [indent + f"exact {numeric_name}"]
        return result + [indent + f"change Complete {ctx_name} ∧ ∀ t, IntegerZeroSpanValid",
                         indent + f"  starIntegerSubsetForms {ctx_name} (C (contextSigns {ctx_name}) t) (den{i} t) (lambda{i} t)",
                         indent + f"have hs : contextSigns {ctx_name} = pattern{i} := rfl",
                         indent + f"rw [hs, h{i}]", indent + f"exact {numeric_name}"]
    result = [indent + "refine ⟨?_, ?_, ?_⟩"]
    for sign, child in zip((-1, 0, 1), node.children):
        child_context = f"Function.update ({context}) {node.depth} (some {SIGNS[sign]})"
        child_lines = direct_valid_proof(child, child_context, indent + "  ")
        result.append(indent + "· " + child_lines[0][len(indent)+2:])
        result.extend(child_lines[1:])
    return result


def unique_rows(leaf: Solved):
    keys, indices, seen = [], [], {}
    for c, w in zip(leaf.coefficients, leaf.multipliers):
        den, wi = cleared(w)
        key = (c, den, wi)
        if key not in seen:
            seen[key] = len(keys)
            keys.append(key)
        indices.append(seen[key])
    return keys, indices


def direct_integer_data_declarations(tree: Node) -> list[str]:
    solved, impossible = terminals(tree)
    lines = []
    for leaf in solved:
        i = leaf.index
        keys, indices = unique_rows(leaf)
        u = len(keys)
        coeff = tuple(key[0] for key in keys)
        den = tuple(Fraction(key[1]) for key in keys)
        weights = tuple(key[2] for key in keys)
        index_body = Lean.balanced_table(indices, lambda j: str(j))
        den_body = Lean.balanced_table(den, Lean.integer)
        lines.extend([
            f"def pattern{i} : Fin 15 → Sign := {Lean.pattern(leaf.pattern)}",
            f"def rowIndex{i} : Fin 80 → Fin {u} := fun {'t' if 't.val' in index_body else '_'} => {index_body}",
            f"def baseCoeff{i} : Fin {u} → Fin 4 → ℤ :=\n  {Lean.integer_matrix(coeff)}",
            f"def baseDen{i} : Fin {u} → ℤ := fun {'t' if 't.val' in den_body else '_'} => {den_body}",
            f"def baseLambda{i} : Fin {u} → Fin 15 → ℤ :=\n  {Lean.integer_matrix(weights)}",
            f"def coeff{i} (t : Fin 80) : Fin 4 → ℤ := baseCoeff{i} (rowIndex{i} t)",
            f"def den{i} (t : Fin 80) : ℤ := baseDen{i} (rowIndex{i} t)",
            f"def lambda{i} (t : Fin 80) : Fin 15 → ℤ := baseLambda{i} (rowIndex{i} t)"])
    for leaf in impossible:
        _, weights = cleared(leaf.weights)
        lines.append(f"def weights{leaf.index} : Fin 15 → ℤ := {Lean.integers(weights)}")
    return lines


def emit_direct_chunk(chunk: Chunk, input_sha: str, label: str | None = None,
                      numeric_style: str = "reflection") -> Path:
    solved, impossible = terminals(chunk.tree)
    name = Lean.ident(label or f"Chunk{chunk.index:04d}")
    header = f'''import MaxCaterpillar.Frontier.StarCertificate.Checker
import MaxCaterpillar.Frontier.StarCertificate.XiInteger
/-! Generated by emit_checker_tree.py --chunks; input SHA256 {input_sha}.
Complete bounded subtree at depth {len(chunk.prefix)}. Stored coefficients
are checked at each leaf; no repeated semantic-target lookup is performed
inside the integer arithmetic. The structural combiner checks all branches.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.Generated.{name}
open BigOperators
def regionContext : Context 15 := {Lean.context(chunk.prefix)}
'''
    lines = direct_integer_data_declarations(chunk.tree)
    for leaf in solved:
        i = leaf.index
        numeric_proof = "(by with_unfolding_all rfl)"
        if numeric_style == "norm_num":
            numeric_proof = f'''(by norm_num [integerSolvedCheck, completeCheck, integerZeroSpanCheck,
      finAll, intSum, starIntegerSubsetForms, solvedContext{i}, pattern{i},
      baseCoeff{i}, baseDen{i}, baseLambda{i}])'''
        lines.extend([
            f"def solvedContext{i} : Context 15 := fun j => some (pattern{i} j)",
            f'''theorem baseNumeric{i} : Complete solvedContext{i} ∧ ∀ t, IntegerZeroSpanValid
    starIntegerSubsetForms solvedContext{i} (baseCoeff{i} t) (baseDen{i} t) (baseLambda{i} t) :=
  (integerSolvedCheck_eq_true starIntegerSubsetForms solvedContext{i} baseCoeff{i} baseDen{i} baseLambda{i}).mp
    {numeric_proof}''',
            f'''theorem solvedNumeric{i} : Complete solvedContext{i} ∧ ∀ t, IntegerZeroSpanValid
    starIntegerSubsetForms solvedContext{i} (coeff{i} t) (den{i} t) (lambda{i} t) :=
  ⟨baseNumeric{i}.1, fun t => baseNumeric{i}.2 (rowIndex{i} t)⟩'''])
    for leaf in impossible:
        i = leaf.index
        numeric_proof = "(by with_unfolding_all rfl)"
        if numeric_style == "norm_num":
            numeric_proof = f'''(by norm_num [integerFarkasCheck, strictNonnegCheck, strictPositiveCheck,
      finAll, finAny, intSum, integerOriented, starIntegerSubsetForms,
      excludedContext{i}, weights{i}])'''
        lines.extend([
            f"def excludedContext{i} : Context 15 := {Lean.context(leaf.prefix)}",
            f'''theorem excludedNumeric{i} : IntegerFarkasValid starIntegerSubsetForms excludedContext{i} weights{i} :=
  (integerFarkasCheck_eq_true starIntegerSubsetForms excludedContext{i} weights{i}).mp
    {numeric_proof}'''])
    lines.append("def tree : IntegerCertificateTree 15 80 :=\n  " + tree_term(chunk.tree))
    binders = "\n".join(f"    (h{leaf.index} : C pattern{leaf.index} = coeff{leaf.index})" for leaf in solved)
    lines.append(f'''theorem valid (C : (Fin 15 → Sign) → Fin 80 → Fin 4 → ℤ)
{binders} : tree.Valid starIntegerSubsetForms C regionContext := by
''' + "\n".join(direct_valid_proof(chunk.tree, "regionContext")))
    lines.append(f"#print axioms valid\nend MaxCaterpillar.Frontier.StarCertificate.Generated.{name}")
    path = OUT / (name + ".lean")
    atomic(path, header + "\n\n".join(lines) + "\n")
    return path


def top_proof(node, context: str, leaf_count: int, indent: str = "  ") -> list[str]:
    if isinstance(node, Chunk):
        solved, _ = terminals(node.tree)
        label = f"Chunk{node.index:04d}"
        result = [indent + f"have hp : ({context}) = {label}.regionContext :=",
                  indent + "  of_decide_eq_true (by with_unfolding_all rfl)",
                  indent + "rw [hp]", indent + f"apply {label}.valid C"]
        for leaf in solved:
            result.extend([indent + f"· have hi := hC ({leaf.index} : Fin {leaf_count})",
                           indent + f"  change C {label}.pattern{leaf.index} = {label}.coeff{leaf.index} at hi",
                           indent + "  exact hi"])
        return result
    if isinstance(node, Impossible):
        return [indent + f"exact (integerFarkasCheck_eq_true starIntegerSubsetForms ({context}) weights{node.index}).mp",
                indent + "  (by with_unfolding_all rfl)"]
    if isinstance(node, Solved):
        raise ValueError("A solved leaf escaped the bounded partition")
    result = [indent + "refine ⟨?_, ?_, ?_⟩"]
    for sign, child in zip((-1, 0, 1), node.children):
        child_context = f"Function.update ({context}) {node.depth} (some {SIGNS[sign]})"
        child_lines = top_proof(child, child_context, leaf_count, indent + "  ")
        result.append(indent + "· " + child_lines[0][len(indent)+2:])
        result.extend(child_lines[1:])
    return result


def emit_assembly(chunks: list[Chunk], top, input_sha: str, label: str = "Full",
                  initial_prefix: tuple[int, ...] = ()) -> Path:
    catalog = {}
    for chunk in chunks:
        for leaf in terminals(chunk.tree)[0]:
            catalog[leaf.index] = chunk.index
    if sorted(catalog) != list(range(len(catalog))):
        raise ValueError("Solved catalog is not a complete interval")
    count = len(catalog)
    imports = "\n".join(f"import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.Chunk{c.index:04d}" for c in chunks)
    label = Lean.ident(label)
    root_context = "regionContext" if initial_prefix else "emptyContext 15"
    header = f'''{imports}

/-! Generated by emit_checker_tree.py --chunks; input SHA256 {input_sha}.
The top skeleton has all three branches at every split. Every numerical
subtree is imported with its checked certificate; no face-list completeness
is assumed. Concrete star-coefficient agreement is a separate finite check.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.Generated.{label}
open BigOperators
'''
    if initial_prefix:
        header += f"def regionContext : Context 15 := {Lean.context(initial_prefix)}\n"
    pattern_cases = "\n".join(f"  | {i} => Chunk{catalog[i]:04d}.pattern{i}" for i in range(count))
    coeff_cases = "\n".join(f"  | {i} => Chunk{catalog[i]:04d}.coeff{i}" for i in range(count))
    lines = [f"def patterns (i : Fin {count}) : Fin 15 → Sign :=\n  match i.val with\n{pattern_cases}\n  | _ => fun _ => .zero",
             f"def coefficients (i : Fin {count}) : Fin 80 → Fin 4 → ℤ :=\n  match i.val with\n{coeff_cases}\n  | _ => 0"]
    def top_excluded(node):
        if isinstance(node, Chunk):
            return []
        if isinstance(node, Impossible):
            return [node]
        if isinstance(node, Solved):
            raise ValueError("Solved leaf outside chunk")
        return [leaf for child in node.children for leaf in top_excluded(child)]
    for leaf in top_excluded(top):
        _, weights = cleared(leaf.weights)
        lines.append(f"def weights{leaf.index} : Fin 15 → ℤ := {Lean.integers(weights)}")
    lines.append("def tree : IntegerCertificateTree 15 80 :=\n  " + tree_term(top))
    lines.append(f'''theorem valid (C : (Fin 15 → Sign) → Fin 80 → Fin 4 → ℤ)
    (hC : ∀ i : Fin {count}, C (patterns i) = coefficients i) :
    tree.Valid starIntegerSubsetForms C ({root_context}) := by
''' + "\n".join(top_proof(top, root_context, count)))
    lines.append('''theorem canonical_forms : integerForms starIntegerSubsetForms = subsetForms := by
  funext j i
  exact starIntegerSubsetForms_cast j i''')
    if initial_prefix:
        lines.append(f'''theorem all_real_on_prefix (C : (Fin 15 → Sign) → Fin 80 → Fin 4 → ℤ)
    (hC : ∀ i : Fin {count}, C (patterns i) = coefficients i)
    (x : Fin 4 → ℝ) (hx : Holds subsetForms regionContext x) :
    ∀ t, evalForm (fun j => (C (actualSigns subsetForms x) t j : ℚ)) x = 0 := by
  have hp : Holds (integerForms starIntegerSubsetForms) regionContext x := by
    rw [canonical_forms]
    exact hx
  have hv := tree.rational_valid starIntegerSubsetForms C regionContext (valid C hC)
  have he := tree.rational.valid_sound (integerForms starIntegerSubsetForms)
    (fun s t i => (C s t i : ℚ)) regionContext hv x hp
  simpa only [canonical_forms] using he

#print axioms all_real_on_prefix
end MaxCaterpillar.Frontier.StarCertificate.Generated.{label}''')
    else:
        lines.append(f'''theorem all_real (C : (Fin 15 → Sign) → Fin 80 → Fin 4 → ℤ)
    (hC : ∀ i : Fin {count}, C (patterns i) = coefficients i) :
    ∀ x : Fin 4 → ℝ, ∀ t,
      evalForm (fun j => (C (actualSigns subsetForms x) t j : ℚ)) x = 0 := by
  intro x t
  have he := tree.all_real_of_valid starIntegerSubsetForms C (valid C hC) x t
  simpa only [canonical_forms] using he

#print axioms all_real
end MaxCaterpillar.Frontier.StarCertificate.Generated.{label}''')
    path = OUT / (label + ".lean")
    atomic(path, header + "\n\n".join(lines) + "\n")
    return path


def emit_chunks(tree: Node, input_path: Path, limit: int | None, max_terms: int, max_solved: int,
                probe_index: int | None = None, numeric_style: str = "reflection") -> list[Path]:
    chunks, top = partition(tree, max_terms, max_solved)
    selected = chunks if limit is None else chunks[:limit]
    sha = hashlib.sha256(input_path.read_bytes()).hexdigest()
    if probe_index is not None:
        return [emit_direct_chunk(chunks[probe_index], sha, f"Probe{probe_index:04d}", numeric_style)]
    paths = [emit_direct_chunk(c, sha, numeric_style=numeric_style) for c in selected]
    if limit is None:
        paths.append(emit_assembly(chunks, top, sha))
    record = {"input_sha256": sha,
              "producer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "total_chunks": len(chunks), "emitted_chunks": len(selected),
              "max_terminals": max_terms, "max_solved": max_solved,
              "numeric_style": numeric_style,
              "full_tree_assembly_emitted": limit is None,
              "outputs": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}}
    atomic(input_path.with_name("checker_chunks_generation.json"), json.dumps(record, indent=2) + "\n")
    return paths


def emit_pilot(tree: Node, input_path: Path, max_terms: int, max_solved: int) -> Path:
    chunks, top = partition(tree, max_terms, max_solved)
    prefix = (-1,) * 7
    for _ in prefix:
        if not isinstance(top, Branch):
            raise ValueError("Pilot path reached a chunk too early")
        top = top.children[0]
    selected = []
    def collect(node):
        if isinstance(node, Chunk):
            selected.append(node)
        elif isinstance(node, Branch):
            for child in node.children:
                collect(child)
    collect(top)
    sha = hashlib.sha256(input_path.read_bytes()).hexdigest()
    path = emit_assembly(selected, top, sha, "Pilot", prefix)
    atomic(input_path.with_name("checker_pilot_generation.json"),
           json.dumps({"input_sha256": sha, "prefix": prefix,
                       "chunks": [x.index for x in selected],
                       "output": str(path.relative_to(ROOT)),
                       "output_sha256": hashlib.sha256(path.read_bytes()).hexdigest()}, indent=2) + "\n")
    return path


def emit_half(tree: Node, input_path: Path, max_terms: int, max_solved: int) -> Path:
    _, top = partition(tree, max_terms, max_solved)
    if not isinstance(top, Branch) or top.depth != 0:
        raise ValueError("Half certificate requires the canonical first-form root split")
    negative, zero = top.children[:2]
    selected = []
    def collect(node):
        if isinstance(node, Chunk):
            selected.append(node)
        elif isinstance(node, Branch):
            for child in node.children:
                collect(child)
    collect(negative)
    collect(zero)
    catalog = {}
    for chunk in selected:
        for leaf in terminals(chunk.tree)[0]:
            catalog[leaf.index] = chunk.index
    count = len(catalog)
    if sorted(catalog) != list(range(count)) or count != 900:
        raise ValueError("Unexpected root-nonpositive leaf catalog")
    imports = "\n".join(f"import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.Chunk{c.index:04d}" for c in selected)
    sha = hashlib.sha256(input_path.read_bytes()).hexdigest()
    header = f'''{imports}
import MaxCaterpillar.Frontier.StarCertificate.Checker.Even
/-! Generated by emit_checker_tree.py --half; input SHA256 {sha}.
Every negative/zero root branch is checked. Actual evenness of the represented
target extends this closed-halfspace certificate to all real vectors. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.Generated.Half
open BigOperators
'''
    pattern_cases = "\n".join(f"  | {i} => Chunk{catalog[i]:04d}.pattern{i}" for i in range(count))
    coeff_cases = "\n".join(f"  | {i} => Chunk{catalog[i]:04d}.coeff{i}" for i in range(count))
    lines = [f"def patterns (i : Fin {count}) : Fin 15 → Sign :=\n  match i.val with\n{pattern_cases}\n  | _ => fun _ => .zero",
             f"def coefficients (i : Fin {count}) : Fin 80 → Fin 4 → ℤ :=\n  match i.val with\n{coeff_cases}\n  | _ => 0"]
    def outside(node):
        if isinstance(node, Chunk):
            return []
        if isinstance(node, Impossible):
            return [node]
        if isinstance(node, Solved):
            raise ValueError("Solved leaf outside half chunk")
        return [a for child in node.children for a in outside(child)]
    for leaf in outside(negative) + outside(zero):
        _, weights = cleared(leaf.weights)
        lines.append(f"def weights{leaf.index} : Fin 15 → ℤ := {Lean.integers(weights)}")
    for name, sign, subtree in (("negative", -1, negative), ("zero", 0, zero)):
        context = f"Function.update (emptyContext 15) 0 (some {SIGNS[sign]})"
        lines.append(f"def {name}Tree : IntegerCertificateTree 15 80 :=\n  {tree_term(subtree)}")
        lines.append(f'''theorem {name}_valid (C : (Fin 15 → Sign) → Fin 80 → Fin 4 → ℤ)
    (hC : ∀ i : Fin {count}, C (patterns i) = coefficients i) :
    {name}Tree.Valid starIntegerSubsetForms C ({context}) := by
''' + "\n".join(top_proof(subtree, context, count)))
    footer = f'''
theorem canonical_forms : integerForms starIntegerSubsetForms = subsetForms := by
  funext j i
  exact starIntegerSubsetForms_cast j i

theorem first_form (x : Fin 4 → ℝ) : evalForm (subsetForms 0) x = x 0 := by
  simp [evalForm, subsetForms, Fin.sum_univ_succ]

theorem nonpositive (C : (Fin 15 → Sign) → Fin 80 → Fin 4 → ℤ)
    (hC : ∀ i : Fin {count}, C (patterns i) = coefficients i)
    (x : Fin 4 → ℝ) (hx : x 0 ≤ 0) :
    ∀ t, evalForm (fun j => (C (actualSigns subsetForms x) t j : ℚ)) x = 0 := by
  rcases lt_or_eq_of_le hx with hn | hz
  · have hp : Holds (integerForms starIntegerSubsetForms)
        (Function.update (emptyContext 15) 0 (some .neg)) x :=
      holds_update _ _ _ (holds_empty _ _) 0 .neg (by
        change evalForm ((integerForms starIntegerSubsetForms) 0) x < 0
        rw [canonical_forms, first_form]
        exact hn)
    have hv := negativeTree.rational_valid starIntegerSubsetForms C _ (negative_valid C hC)
    have he := negativeTree.rational.valid_sound (integerForms starIntegerSubsetForms)
      (fun s t i => (C s t i : ℚ)) _ hv x hp
    simpa only [canonical_forms] using he
  · have hp : Holds (integerForms starIntegerSubsetForms)
        (Function.update (emptyContext 15) 0 (some .zero)) x :=
      holds_update _ _ _ (holds_empty _ _) 0 .zero (by
        change evalForm ((integerForms starIntegerSubsetForms) 0) x = 0
        rw [canonical_forms, first_form]
        exact hz)
    have hv := zeroTree.rational_valid starIntegerSubsetForms C _ (zero_valid C hC)
    have he := zeroTree.rational.valid_sound (integerForms starIntegerSubsetForms)
      (fun s t i => (C s t i : ℚ)) _ hv x hp
    simpa only [canonical_forms] using he

theorem all_real (C : (Fin 15 → Sign) → Fin 80 → Fin 4 → ℤ)
    (hC : ∀ i : Fin {count}, C (patterns i) = coefficients i)
    (heven : ∀ (x : Fin 4 → ℝ) t,
      evalForm (fun j => (C (actualSigns subsetForms (-x)) t j : ℚ)) (-x) =
      evalForm (fun j => (C (actualSigns subsetForms x) t j : ℚ)) x) :
    ∀ x : Fin 4 → ℝ, ∀ t,
      evalForm (fun j => (C (actualSigns subsetForms x) t j : ℚ)) x = 0 := by
  intro x t
  exact even_zero_of_nonpositive_coordinate 0
    (fun y => evalForm (fun j => (C (actualSigns subsetForms y) t j : ℚ)) y)
    (fun y => heven y t) (fun y hy => nonpositive C hC y hy t) x

#print axioms all_real
end MaxCaterpillar.Frontier.StarCertificate.Generated.Half
'''
    path = OUT / "Half.lean"
    atomic(path, header + "\n\n".join(lines) + "\n" + footer)
    record = {"input_sha256": sha, "producer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "chunks": [c.index for c in selected], "chunk_stop_before": max(c.index for c in selected)+1,
              "solved_faces": count, "output": str(path.relative_to(ROOT)),
              "output_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
              "scope": "All real vectors after independently proved evenness; all root-negative and root-zero branches checked."}
    atomic(input_path.with_name("checker_half_generation.json"), json.dumps(record, indent=2)+"\n")
    return path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=INPUT)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--smoke", action="store_true")
    mode.add_argument("--integer-smoke", action="store_true")
    mode.add_argument("--target-benchmark", action="store_true")
    mode.add_argument("--chunks", action="store_true")
    mode.add_argument("--pilot", action="store_true")
    mode.add_argument("--half", action="store_true")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--max-terminals", type=int, default=127)
    parser.add_argument("--max-solved", type=int, default=16)
    parser.add_argument("--probe-index", type=int)
    parser.add_argument("--arithmetic", choices=("reflection", "norm_num"), default="reflection")
    args = parser.parse_args()
    tree, data = load(args.input)
    if args.chunks:
        paths = emit_chunks(tree, args.input, args.limit, args.max_terminals, args.max_solved,
                            args.probe_index, args.arithmetic)
        print(json.dumps({"output_count": len(paths), "first": str(paths[0].relative_to(ROOT)),
                          "last": str(paths[-1].relative_to(ROOT))}))
        return
    if args.half:
        output = emit_half(tree, args.input, args.max_terminals, args.max_solved)
    elif args.pilot:
        output = emit_pilot(tree, args.input, args.max_terminals, args.max_solved)
    elif args.target_benchmark:
        output = emit_target_benchmark(tree, args.input)
    elif args.integer_smoke:
        output = emit_integer_smoke(tree, args.input)
    else:
        output = emit_smoke(tree, args.input)
    print(json.dumps({"output": str(output.relative_to(ROOT)),
                      "solved": len(data["leaves"]), "excluded": len(data["excluded"])}))


if __name__ == "__main__":
    main()
