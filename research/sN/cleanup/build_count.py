#!/usr/bin/env python3
"""Assemble `MaxCaterpillar/Count/*.lean` from the pruned superseded sources.

Run once by the cleanup pass (commit a503f01 + rationality cleanup).  STAGE holds the
output of `prune.py` (declarations unreachable from the public theorems removed); ORIG is
the repository before the move (for the declarations re-added to replace primed copies).
"""
import os
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).parent))
from assemble import get  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[3]
STAGE = pathlib.Path(os.environ['STAGE'])


def staged(rel):
    return (STAGE / rel.replace('/', '__')).read_text()


def body(rel):
    """Text between the first `namespace` line and the matching final `end`."""
    t = staged(rel)
    lines = t.split('\n')
    i = next(j for j, l in enumerate(lines) if l.startswith('namespace '))
    ns = lines[i].split()[1]
    k = max(j for j, l in enumerate(lines) if l.strip() == f'end {ns}')
    return '\n'.join(lines[i + 1:k]).strip('\n'), ns


def drop_opens(text):
    """Drop the leading `open` lines (with continuation lines) of a body."""
    lines = text.split('\n')
    out, skipping = [], True
    for l in lines:
        if skipping and (l.startswith('open ') or (l.startswith('  ') and out == [] and l.strip())):
            continue
        if skipping and l.strip() == '':
            continue
        skipping = False
        out.append(l)
    return '\n'.join(out)


def remove_block(text, start, end_line):
    """Remove the first block starting with line `start` through line `end_line`."""
    i = text.index(start)
    j = text.index(end_line, i) + len(end_line)
    return text[:i] + text[j:]


def tidy(text):
    text = re.sub(r'\n{3,}', '\n\n', text)
    # empty sections / namespaces
    for _ in range(3):
        text = re.sub(r'(/-! [^\n]*-/\n\n)?section (\w+)\n\n(variable [^\n]*\n\n)?end \2\n', '', text)
        text = re.sub(r'(/-! [^\n]*-/\n\n)?namespace (\w+)\n\n(variable [^\n]*\n\n)?end \2\n', '', text)
    text = re.sub(r'\n{3,}', '\n\n', text)
    return text


def write(rel, header, text):
    p = ROOT / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(tidy(header.rstrip('\n') + '\n\n' + text.strip('\n') + '\n'))
    print('wrote', rel, len(p.read_text().split('\n')))


DEPRIME = ['mem_tieSet', 'basePtR_of_mem', 'basePtR_le_neg_one', 'boxPt_of_mem',
           'boxPt_of_not_mem', 'boxPt_insert_of_ne', 'mixedDiff_congr',
           'mixedDiff_eq_zero_of_insert', 'mixedDiff_eq_zero_of_two', 'abs_boxPt_sub_le',
           'abs_relu_sub_le']


def deprime(text):
    for n in DEPRIME:
        text = re.sub(rf"\b{n}'", n, text)
    return text


def locality():
    parts = []
    for rel in ['MaxCaterpillar/CountExp/Defs.lean', 'MaxCaterpillar/CountExp/W1Functional.lean',
                'MaxCaterpillar/CountExp/W2Digits.lean', 'MaxCaterpillar/CountExp/W4Orders.lean']:
        b, _ = body(rel)
        parts.append(drop_opens(b))
    text = '\n\n'.join(parts)
    text = text.replace('private theorem', 'theorem').replace('private def', 'def')
    text = remove_block(text, '/-! ## Normalized keys in full coordinates', 'end Path\n')
    text = remove_block(text, '/-! ## The hinge forest as a rooted forest -/', 'end HingeCat\n')
    i = text.index('theorem mem_tieSet {N k : ℕ}')
    j = text.index('theorem subtypeCongr_apply_pos')
    w4 = text[i:j]
    text = text[:i] + text[j:]
    i = text.index('theorem mem_tieSet {o : Fin N}')
    j = text.index('theorem basePtR_of_mem')
    text = text[:i] + w4.replace('{N k : ℕ} {π : Equiv.Perm (Fin N)} ', '').replace(
        '{N k : ℕ} (hk', '(hk') + text[j:]
    rs = 'MaxCaterpillar/Trees/RootedStars.lean'
    box = deprime(get(rs, "basePtR_le_neg_one'") + '\n\n' + get(rs, "boxPt_of_not_mem'"))
    text = text.replace('\nend Box\n', '\n' + box + '\n\nend Box\n', 1)
    core = deprime(get(rs, "mixedDiff_congr'"))
    text = text.replace('\nend Core\n', '\n' + core + '\n\nend Core\n', 1)
    text = text.replace('card_tieSet_W1', 'card_tieSet')
    text = text.replace('theorem subtypeCongr_apply_pos', 'open scoped Nat\n\ntheorem subtypeCongr_apply_pos', 1)
    text = text.replace('variable {r : ℕ}\n\nend Pass', 'end Pass')
    header = '''import MaxCaterpillar.Compilation
import Mathlib.LinearAlgebra.Pi

/-!
# Localities and the mixed finite difference

A *locality* of a permutation `π` of the coordinates and `k ≤ N` is the tie set
`T = {o : π o < k}` with the base point `0` on `T` and `-B^(π o)` elsewhere.  The `k`-th
mixed finite difference at the base point (`mixedDiff`) kills the auxiliary functions
(`mixedDiff_auxiliary`), takes the value `-(-1)^k δ` on the maximum (`mixedDiff_maximum`),
and kills every function that does not depend on some tie coordinate.  The digit argument
(`digits_eq_zero`, `basePtR_anti`) and the fiber count (`card_fiber_pairsOrdered`) are the
two combinatorial inputs of the per-unit counts.
-/

open BigOperators Finset

namespace MaxCaterpillar.Count

open MaxNN MaxNN.Width MaxNN.Caterpillar MaxNN.Caterpillar.Corrections MaxNN.ParamidGeom
  MaxNN.ParamidChain
'''
    write('MaxCaterpillar/Count/Locality.lean', header, text + '\n\nend MaxCaterpillar.Count')



def cut(text, name):
    """Remove the declaration chunk (with docstring) of `name` from text; return (text, chunk)."""
    from prune import split_commands, classify
    cmds = split_commands(text)
    out, chunk = [], None
    for c in cmds:
        kind, info = classify(c)
        if kind == 'decl' and info[1] == name and chunk is None:
            chunk = '\n'.join(c).rstrip()
            continue
        out.append('\n'.join(c))
    if chunk is None:
        raise SystemExit(f'cut: {name} not found')
    return '\n'.join(out), chunk


TREES_OPEN = 'open MaxNN CountLower Count'
COUNT_OPEN = 'open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections CountLower Trees'


def sub_body(rel):
    b, _ = body(rel)
    b = drop_opens(b)
    b = b.replace('private theorem', 'theorem').replace('private def', 'def')
    return deprime(b)


def passing():
    desc = sub_body('MaxCaterpillar/Trees/DescrPass.lean')
    desc, dadj = cut(desc, 'DAdj')
    desc, dkappa = cut(desc, 'DKappa')
    bd = sub_body('MaxCaterpillar/Trees/BoundedDegree.lean')
    bd, incid = cut(bd, 'incid')
    bdm = sub_body('MaxCaterpillar/Trees/BoundedDegreeMain.lean')
    k = bdm.index('namespace TreeFace')
    bdm_main, bdm_tf = bdm[:k], bdm[k:]
    bdm_tf, hdeg = cut(bdm_tf, 'hingeDeg')
    hubs = sub_body('MaxCaterpillar/Trees/Hubs.lean')
    hubsmain = sub_body('MaxCaterpillar/Trees/HubsMain.lean')
    hubsmain = hubsmain.replace('end MaxCaterpillar.Trees', '').replace('namespace MaxCaterpillar.Trees', '')
    hubsmain = re.sub(r'\nopen MaxNN CountLower CountExp\n', '\n', hubsmain)
    header = """import MaxCaterpillar.Count.Defs
import MaxCaterpillar.Count.Locality

/-!
# The pass conditions for unit descriptions

A description `D = (h, M)` (`CountLower.Descr`, pairs `m.1 < m.2`) *passes* the locality of
`π` (`DPasses`) if every coordinate outside the tie set has exactly `κ_o` hinge neighbours
above it (balanced) and every tie coordinate without a tied hinge neighbour has `κ ≠ 0`
(active).  A unit whose mixed difference is nonzero passes (`descr_pass_of_mixedDiff_ne`),
so every locality is passed by some unit of an expansion (`exists_dpasses`).  Balanced
orders are determined on the forest by its orientation (`orient_eq_of_balanced`), and a
matching of untied edges halves the balanced fiber (`card_balanced_fiber_of_matching`).
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Trees

""" + TREES_OPEN + '\n\nvariable {N : ℕ}\n'
    write('MaxCaterpillar/Count/Passing.lean', header,
          desc + '\n\n' + bd + '\n\n' + bdm_main + '\n\n' + hubs + '\n\nend MaxCaterpillar.Trees')
    header2 = """import MaxCaterpillar.Count.Passing

/-!
# Tree face descriptions as hinge forests

The description of a tree face `F` has ordered pairs (`descr_lt`), satisfies the leaf
property (`descr_leaf`), and every pair has a *child* endpoint, injectively
(`descr_child_spec`, `descr_child_inj`).  `starFace a c` is the rooted star of Brunck et al.
as a tree face.
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Trees

""" + TREES_OPEN + '\n'
    write('MaxCaterpillar/Count/TreeForest.lean', header2,
          bdm_tf + '\n\n' + hubsmain + '\n\nend MaxCaterpillar.Trees')
    return dadj, dkappa, incid, hdeg


def perunit():
    red = sub_body('MaxCaterpillar/Simplify/Reduced.lean')
    red, nbrs = cut(red, 'nbrs')
    uni = sub_body('MaxCaterpillar/Simplify/Unified.lean')
    uni, ol = cut(uni, 'IsOLeaf')
    uni, td = cut(uni, 'trunkDeg')
    uni, om = cut(uni, 'OmegaLe')
    header = """import MaxCaterpillar.Count.Passing
import MaxCaterpillar.Count.StarCover
import MaxCaterpillar.Count.BlockSum

/-!
# The per-unit count

For a description `D` with ordered pairs and the leaf property, `card_passes_le_cover`
bounds the number of orders passed by `D` through any covering relation of the free
vertices, and `card_passes_le_unified` specializes it to the relation of out-leaf edges and
heir edges: if `ω ≤ Δ` (`OmegaLe D Δ`, `Δ ≥ 2`), at most `(2Δ+2)^k k! (N-k)!` orders of the
`N!` pass `D` at level `k`.
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Count

""" + COUNT_OPEN + '\n'
    write('MaxCaterpillar/Count/PerUnit.lean', header, red + '\n\n' + uni + '\n\nend MaxCaterpillar.Count')
    return nbrs, ol, td, om


def classes():
    tu = sub_body('MaxCaterpillar/Simplify/TreeUnits.lean')
    tu = tu.replace('TreeFaceR.', 'TreeFace.')
    tu, star = cut(tu, 'IsStarFace')
    tu, upc = cut(tu, 'IsUpCaterpillar')
    k = tu.index('namespace TreeFaceR')
    pre = tu[:k].strip()
    tu = tu[k:]
    tu = re.sub(r'namespace TreeFaceR\n', '', tu, count=1)
    tu = tu.replace('end TreeFaceR', '', 1)
    tu = re.sub(r'namespace TreeFaceR\n+end TreeFaceR\n?', '', tu)
    tu = tu.replace('open Classical\n', '', 1).replace('variable {N : ℕ} (F : TreeFace N)\n', '', 1)
    br = sub_body('MaxCaterpillar/Simplify/Brunck.lean').replace('TreeFaceR.', 'TreeFace.')
    br, bexp = cut(br, 'IsBrunckExpansion')
    um = sub_body('MaxCaterpillar/Simplify/UnifiedMain.lean').replace('TreeFaceR.', 'TreeFace.')
    k = um.index('end Class')
    cls = um[:k + len('end Class')]
    rest = um[k + len('end Class'):]
    header = """import MaxCaterpillar.Count.PerUnit
import MaxCaterpillar.Count.TreeForest
import MaxCaterpillar.Audit.CaterpillarTree

/-!
# The class `ω ≤ Δ`

Units with a reduced forest of degree `≤ Δ` satisfy `ω ≤ Δ` (`omegaLe_of_redDeg`): the
caterpillar tree faces (`redDeg_of_isUpCaterpillar`, `Δ = 2`), the faces of the rooted stars
of Brunck et al. (`redDeg_of_isStar`), and the trees of hinge degree `≤ Δ`
(`redDeg_of_hingeDeg_le`).  Units with at most `s` out-leaves at each vertex satisfy
`ω ≤ s + 1` (`omegaLe_of_outLeafBound`).  Every caterpillar function is the face function of
a caterpillar tree with `x_parent - x_leaf` on its leaves (`caterpillarFunction_eq_upTree`).
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Trees.TreeFace

open MaxNN CountLower Count
open Classical

variable {N : ℕ} (F : TreeFace N)
"""
    assert pre == '' or pre.startswith('/-!'), pre[:200]
    text = (pre + '\n\n' if pre else '') + tu + '\n\nend MaxCaterpillar.Trees.TreeFace\n\nnamespace MaxCaterpillar.Count\n\nopen MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections CountLower Trees Audit\n\n' + br + '\n\n' + cls + '\n\nend MaxCaterpillar.Count'
    write('MaxCaterpillar/Count/Classes.lean', header, text)
    return star, upc, bexp, rest


def main_all():
    dadj, dkappa, incid, hdeg = passing()
    nbrs, ol, td, om = perunit()
    star, upc, bexp, rest = classes()
    comb = sub_body('MaxCaterpillar/Trees/Combined.lean')
    _, mixed = cut(comb, 'IsMixedExpansion')
    cov = sub_body('MaxCaterpillar/Simplify/Coverage.lean')
    _, outleaf = cut(cov, 'IsOutLeaf')
    _, olb = cut(cov, 'OutLeafBound')
    indent = lambda s: s
    defs = f"""import MaxCaterpillar.Count.TreeFace

/-!
# Definitions for the exponential count

* `IsMixedExpansion r K₁ K₂`: `max_N` (`N = r + 2`) is a linear combination of the
  caterpillar functions of `K₁`, the tree face functions of `K₂` (`Count/TreeFace.lean`),
  and the auxiliary functions.
* `OmegaLe D Δ`: every vertex `v` of the hinge forest of `D` has `ω(v) ≤ Δ`, where `ω(v)`
  (`trunkDeg`) counts the out-leaves adjacent to `v` (leaves with `κ = 1`) plus one if `v`
  has a neighbour of degree `≥ 2`.
* `IsBrunckExpansion`: `IsMixedExpansion` with every tree unit a face of a rooted star of
  Brunck et al. (`TreeFace.IsStarFace`).
* `TreeFace.hingeDeg`, `OutLeafBound`: the two special classes of the corollaries.
-/

open BigOperators Finset

namespace MaxCaterpillar.Trees

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections CountLower

variable {{N : ℕ}}

{dadj}

{dkappa}

{incid}

namespace TreeFace

variable (F : TreeFace N)

{hdeg}

{star}

{upc}

end TreeFace

{mixed}

end MaxCaterpillar.Trees

namespace MaxCaterpillar.Count

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections CountLower Trees

section Class

open Classical

variable {{N : ℕ}}

{nbrs}

{ol}

{td}

{om}

{outleaf}

{olb}

end Class

{bexp}

end MaxCaterpillar.Count
"""
    (ROOT / 'MaxCaterpillar/Count/Defs.lean').write_text(tidy(defs))
    print('wrote Defs')
    cm = sub_body('MaxCaterpillar/Simplify/CoverageMain.lean')
    header = """import MaxCaterpillar.Count.Classes
import Mathlib.Data.Nat.Choose.Cast

/-!
# The exponential count

`unified_choose_le`: if `max_N = Σ_{k ∈ K₁} d_k U_k + Σ_{F ∈ K₂} e_F U_F + (auxiliary)` with
caterpillar functions `U_k` and tree face functions `U_F` with `ω ≤ Δ` (`Δ ≥ 2`), then
`C(N, m) ≤ (2Δ+2)^m (|K₁| + |K₂|)` for `3 ≤ m ≤ N`; `unified_exponential`:
`(2Δ+3)^N ≤ (N+1) (2Δ+2)^N (|K₁| + |K₂|)` for `N ≥ 3`.  Corollaries for caterpillars and the
building blocks of Brunck et al. (base 6), bounded hinge degree, and few out-leaves.
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Count

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections CountLower Trees Audit

variable {N : ℕ}
"""
    write('MaxCaterpillar/Count/Main.lean', header, cm + '\n\n' + rest + '\n\nend MaxCaterpillar.Count')

if __name__ == '__main__':
    for f in sys.argv[1:]:
        globals()[f]()
