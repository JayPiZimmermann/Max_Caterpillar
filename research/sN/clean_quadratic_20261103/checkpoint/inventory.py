#!/usr/bin/env python3
"""Recheck the bounded source inventory; optionally copy only absent paths.

This checks frozen receipt hashes and source scope. It does not rerun Lean,
Ethos, or the mathematical reductions. Run from any working directory.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent.relative_to(ROOT).as_posix()
C = "research/sN/clean_quadratic_20261103"
M = "research/sN/max5_optimal_20261103"
BASE = "82ef24b251327b2e1bfdf92a39c6f6b9e7c6924f"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
RECEIPTS = [
    (f"{C}/normalization/receipt.json", ["source_files", "logs"]),
    (f"{C}/fixed_pairs_audit/paper_review_sources.json", ["sources"]),
    (f"{M}/construction/ten_six/receipt.json", ["source_hashes"]),
    (f"{M}/construction/nine_eleven/receipt.json", ["sources"]),
    (f"{M}/lower/baseline_receipt.json", ["hashes", "source_closure_hashes"]),
    (f"{M}/lower/triple_contact/receipt.json", ["source_files"]),
    (f"{M}/lower/triple_contact/handoff.json", ["files"]),
    (f"{M}/lower/width4_geometry/segment_scalar_receipt.json", ["files"]),
    (f"{M}/audit/recheck.json", ["sources"]),
]
EXTRAS = [
    f"{C}/normalization/README.md", f"{C}/normalization/normalization.md",
    f"{C}/normalization/normalization.tex", f"{C}/normalization/ordinary_linear_bound.md",
    f"{C}/normalization/recheck.py", f"{C}/probability/fixed_pairs.md",
    f"{C}/probability/fixed_pairs.tex", f"{C}/probability/matching/argument.md",
    f"{C}/probability/matching/lemma.tex", f"{C}/matching/AUDIT.md",
    f"{C}/fixed_pairs_audit/AUDIT.md", f"{C}/fixed_pairs_audit/control.py",
    f"{C}/fixed_pairs_audit/control.json", f"{C}/fixed_pairs_audit/PAPER_REVIEW.md",
    "paper/drafts/quadratic_width/main.tex", "paper/drafts/quadratic_width/normalization.tex",
    "paper/drafts/quadratic_width/fixed_pairs.tex", "paper/drafts/quadratic_width/main.pdf",
    "paper/drafts/quadratic_width/main.log",
    f"{M}/construction/ten_six/README.md", f"{M}/construction/nine_eleven/README.md",
    f"{M}/lower/STATUS.md", f"{M}/lower/width4_geometry/segment_obstruction.md",
    f"{M}/lower/width4_geometry/segment_audit.md",
    f"{M}/lower/width4_geometry/check_midpoint_supports.py",
    f"{M}/lower/width4_geometry/midpoint_support_secondary_receipt.json",
    f"{M}/audit/FRONTIER.md", f"{M}/audit/recheck.py",
    f"{M}/audit/four_shared_receipt_inventory.json", f"{M}/audit/pdf/SCOPE.md",
    f"{HERE}/inventory.py", f"{HERE}/AUDIT.md",
]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: str):
    return json.loads((ROOT / path).read_text())


def lean_code(text: str) -> str:
    """Mask nested comments and strings, retaining offsets and newlines."""
    out = list(text)
    i = 0
    while i < len(text):
        if text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0:
                j = len(text)
        elif text.startswith("/-", i):
            j, depth = i + 2, 1
            while j < len(text) and depth:
                if text.startswith("/-", j):
                    depth += 1
                    j += 2
                elif text.startswith("-/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            if depth:
                raise ValueError("unterminated Lean block comment")
        elif text[i] == '"':
            j = i + 1
            while j < len(text):
                if text[j] == "\\":
                    j += 2
                elif text[j] == '"':
                    j += 1
                    break
                else:
                    j += 1
            else:
                raise ValueError("unterminated Lean string")
        else:
            i += 1
            continue
        for k in range(i, j):
            if out[k] != "\n":
                out[k] = " "
        i = j
    return "".join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--publication", type=Path, default=Path("/tmp/max4-proof-publication-20261102"))
    parser.add_argument("--write", action="store_true", help="write selection.json and rootcopy_paths.json")
    parser.add_argument("--copy-new", action="store_true", help="copy absent selected paths only; requires --write")
    args = parser.parse_args()
    if args.copy_new and not args.write:
        parser.error("--copy-new requires --write")
    pub = args.publication.resolve()
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=pub, text=True).strip()
    if head != BASE:
        raise ValueError(f"unexpected publication baseline {head}; expected {BASE}")
    wanted, reasons, receipt_info, axiom_checks = {}, {}, {}, []

    def add(path: str, reason: str, expected: str | None = None):
        rel = Path(path)
        if rel.is_absolute() or ".." in rel.parts:
            raise ValueError(f"non-relative selected path: {path}")
        source = ROOT / rel
        if not source.is_file() or source.is_symlink():
            raise ValueError(f"missing/non-regular source: {path}")
        actual = digest(source)
        if expected is not None and actual != expected:
            raise ValueError(f"receipt mismatch: {path}: {actual} != {expected} ({reason})")
        if path in wanted and wanted[path] != actual:
            raise ValueError(f"source changed during audit: {path}")
        wanted[path] = actual
        reasons.setdefault(path, set()).add(reason)

    def axioms(label: str, values):
        if isinstance(values, str):
            values = [x.strip() for x in values.split(",") if x.strip()]
        if not set(values) <= STANDARD:
            raise ValueError(f"nonstandard axioms {label}: {values}")
        axiom_checks.append({"declaration": label, "axioms": sorted(set(values))})

    for receipt, keys in RECEIPTS:
        d = load(receipt)
        add(receipt, "receipt")
        receipt_info[receipt] = {"status": d["status"], "maps": {k: len(d[k]) for k in keys}}
        for key in keys:
            for path, sha in d[key].items():
                add(path, f"{receipt}:{key}", sha)
        for declaration, values in d.get("headline_axioms", {}).items():
            axioms(declaration, values)
        for entry in d.get("axiom_audits", []) + d.get("claims", []):
            axioms(entry["declaration"], entry["axioms"])
        if "axioms" in d:
            axioms(d.get("theorem", receipt), d["axioms"])
        for entry in d.get("checks", []):
            if entry["exit"] != 0:
                raise ValueError(f"failed recorded check in {receipt}")
            for i, values in enumerate(entry.get("axiom_audits", [])):
                axioms(f"{entry['module']}:{i}", values)

    six = f"{M}/lower/same_label/publication_files.json"
    add(six, "frozen six-case manifest", "1b221f80eb16aace53eb5280809e2e3b0f376fba16523759dfbfb7ee6cb59f30")
    six_d = load(six)
    for group, files in six_d["groups"].items():
        for path, sha in files.items():
            add(path, f"{six}:{group}", sha)
    six_paths = f"{M}/lower/same_label/publication_paths.txt"
    add(six_paths, "frozen six-case paths")
    listed = set((ROOT / six_paths).read_text().splitlines())
    expected_paths = {six, six_paths} | {p for group in six_d["groups"].values() for p in group}
    if listed != expected_paths:
        raise ValueError(f"six-case manifest/path disagreement: {listed ^ expected_paths}")
    receipt_info[six] = {"status": "FROZEN_SIX_CASE_PACKAGE", "groups": {k: len(v) for k, v in six_d["groups"].items()}}

    secondary = f"{M}/lower/width4_geometry/midpoint_support_secondary_receipt.json"
    d = load(secondary)
    add(d["source"], secondary, d["source_sha256"])
    add(f"{M}/lower/width4_geometry/check_midpoint_supports.py", secondary, d["checker_sha256"])
    add(f"{M}/lower/same_label/midpoint_cover_receipt.json", secondary, d["primary_count_sha256"])
    add(f"{M}/audit/recheck.py", "finite frontier checker receipt", load(f"{M}/audit/recheck.json")["checker_sha256"])
    for path in EXTRAS:
        add(path, "explicit bounded checkpoint selection")

    frozen_path = ROOT / HERE / "selection.json"
    if frozen_path.exists() and not args.write:
        frozen = json.loads(frozen_path.read_text())
        frozen_hashes = {p: info["sha256"] for p, info in frozen["artifacts"].items()}
        if frozen_hashes != wanted:
            differences = sorted(p for p in set(frozen_hashes) | set(wanted)
                                 if frozen_hashes.get(p) != wanted.get(p))
            raise ValueError(f"selected sources differ from frozen selection: {differences}")

    lean = sorted(p for p in wanted if p.endswith(".lean"))
    external = set()
    forbidden = re.compile(r"(?<![\w'])\b(?:sorry|admit|sorryAx|axiom|unsafe|native_decide|Lean\.ofReduceBool)\b")
    for path in lean:
        code = lean_code((ROOT / path).read_text())
        bad = forbidden.search(code)
        if bad:
            raise ValueError(f"forbidden Lean construct {path}:{code[:bad.start()].count(chr(10)) + 1}: {bad.group()}")
        for match in re.finditer(r"^\s*(?:public\s+)?import\s+([^\n]+)", code, re.M):
            for module in match.group(1).split():
                dependency = module.replace(".", "/") + ".lean"
                if (ROOT / dependency).is_file():
                    if dependency not in wanted:
                        raise ValueError(f"local import absent from selected closure: {path} -> {dependency}")
                else:
                    external.add(module)

    new, reused = [], []
    for path, sha in sorted(wanted.items()):
        dest = pub / path
        if dest.exists():
            if not dest.is_file() or dest.is_symlink() or digest(dest) != sha:
                raise ValueError(f"existing publication path differs; no overwrite permitted: {path}")
            reused.append(path)
        else:
            new.append(path)
    result = {
        "status": "PASS_SOURCE_HASH_AND_SCOPE_AUDIT",
        "publication_base": BASE,
        "scope": "Frozen receipt/source inventory, lexical Lean scan and local import closure; no fresh full-project Lean build or external certificate replay.",
        "receipts": receipt_info,
        "counts": {"artifacts": len(wanted), "lean_sources": len(lean), "new_paths": len(new), "identical_existing_paths": len(reused), "bytes": sum((ROOT / p).stat().st_size for p in wanted), "recorded_standard_axiom_checks": len(axiom_checks)},
        "axiom_checks": axiom_checks,
        "external_imports_bound_by_lake_manifest": sorted(external),
        "forbidden_construct_scan": "PASS: nested comments and strings excluded",
        "local_import_closure": "PASS",
        "new_paths": new,
        "identical_existing_paths": reused,
        "artifacts": {p: {"sha256": wanted[p], "bytes": (ROOT / p).stat().st_size, "reasons": sorted(reasons[p])} for p in sorted(wanted)},
        "metadata_note": "selection.json and rootcopy_paths.json are excluded from their own hash inventory to avoid self-reference; both are included in rootcopy_paths.json.",
    }
    if args.write:
        for name, value in [("selection.json", result), ("rootcopy_paths.json", sorted(new + [f"{HERE}/selection.json", f"{HERE}/rootcopy_paths.json"]))]:
            dest = ROOT / HERE / name
            data = json.dumps(value, indent=2, sort_keys=True) + "\n"
            # Existing publication metadata must never be silently overwritten.
            if (pub / HERE / name).exists() and (pub / HERE / name).read_text() != data:
                raise ValueError(f"existing publication metadata differs: {name}")
            dest.write_text(data)
    if args.copy_new:
        paths = load(f"{HERE}/rootcopy_paths.json")
        for path in paths:
            source, dest = ROOT / path, pub / path
            expected = wanted.get(path, digest(source))
            if digest(source) != expected:
                raise ValueError(f"source changed before copy: {path}")
            if dest.exists():
                if digest(dest) != expected:
                    raise ValueError(f"existing publication path differs: {path}")
                continue
            dest.parent.mkdir(parents=True, exist_ok=True)
            # Exclusive creation prevents even a concurrent writer being overwritten.
            with source.open("rb") as src, dest.open("xb") as dst:
                shutil.copyfileobj(src, dst)
            if digest(dest) != expected:
                raise ValueError(f"post-copy hash mismatch: {path}")
    print(json.dumps({"status": result["status"], "counts": result["counts"], "copied_new": args.copy_new}, indent=2))


if __name__ == "__main__":
    main()
