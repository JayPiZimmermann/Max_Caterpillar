import Mathlib.Data.Real.Archimedean
import MaxCaterpillar.Definitions
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Nat.Interval

/-! # The building blocks of Brunck–Hertrich–Rueß–Stade–Yehudayoff, Sec. 7.1

Definitions from F. Brunck, C. Hertrich, K. Rueß, J. Stade, A. Yehudayoff,
*Two ReLU layers is all you need*, arXiv:2610.28587v1, Part 2 (Sec. 6 and
Sec. 7.1), stated literally in their indexing:

* `[n]` is `Fin n`, and the standard basis vector `e_k` is `Pi.single k 1`;
* an ordering `π = (π₁, …, π_{n-1})` of `V_{-v} = [n] ∖ {v}` is a bijection from
  the `n - 1` positions onto `V_{-v}`; positions are `1`-based, `π_i = Ordering.pos π i`;
* the marked set `M ⊆ {2, …, n-1}` is a finite set of natural numbers;
* `H_{-v} = {p : p_v = 0, ∑_k p_k = 1}`, `u_i = ∑_{j<i} p_{π_j}`, and
  `B_{v,π,M}` is their Eq. (3);
* `pyr_q(P) = conv({q} ∪ P)` and `h_P(y) = sup_{p ∈ P} ⟨p, y⟩`.

The relation to the caterpillar functions is in `MaxCaterpillar.Competing.Relation`.
-/

open BigOperators

namespace MaxCaterpillar

/-- The caterpillar description `(h_{π,S}, L_{π,S})` of the paper's Definition
`def:caterpillar`: the head `x_{π(q+1)} - x_{π(0)}` and the edge functions
`x_{π(p(j)+1)} - x_{π(j+1)}` (`1 ≤ j ≤ r`) of the word `π` (apex `π 0`) with cut set `S`,
in the reduced coordinates of `FaceKey`. `caterpillarFunction` of it is `U_{π,S}`. -/
noncomputable def caterpillarWordDescription {r : ℕ} (π : Equiv.Perm (Fin (r + 1 + 1)))
    (S : Finset (Fin (r + 1))) : FaceKey r :=
  (MaxNN.Caterpillar.Corrections.rawGamma π S, MaxNN.Caterpillar.Corrections.rawLabels π S)

/-- The support function `h_P(y) = sup_{p ∈ P} ⟨p, y⟩` of a set `P ⊆ ℝⁿ`
(Brunck et al., Sec. 1.1 and Sec. 6). -/
noncomputable def supportFunction {n : ℕ} (P : Set (Fin n → ℝ)) (y : Fin n → ℝ) : ℝ :=
  sSup ((fun p => ∑ k, p k * y k) '' P)

/-- The pyramid `pyr_q(P) := conv({q} ∪ P)` with apex `q` and base `P`
(Brunck et al., Sec. 6). -/
def pyramid {n : ℕ} (q : Fin n → ℝ) (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  convexHull ℝ (insert q P)

/-- The zonotope `a + ∑_{i ∈ I} [0, g_i]`, written parametrically:
the points `a + ∑_{i ∈ I} t_i g_i` with `0 ≤ t_i ≤ 1`. -/
def zonotope {n : ℕ} (a : Fin n → ℝ) (I : Finset ℕ) (g : ℕ → Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {p | ∃ t : ℕ → ℝ, (∀ i ∈ I, 0 ≤ t i ∧ t i ≤ 1) ∧ p = a + ∑ i in I, t i • g i}

namespace BHRSY

variable {n : ℕ}

/-- An ordering `π = (π₁, …, π_{n-1})` of `V_{-v} = [n] ∖ {v}`
(Brunck et al., Sec. 7.1): a bijection from the `n - 1` positions onto `V_{-v}`.
The Lean position `⟨i - 1, _⟩` is their position `i`. -/
abbrev Ordering (n : ℕ) (v : Fin n) := Fin (n - 1) ≃ {k : Fin n // k ≠ v}

/-- The entry `π_i` at the `1`-based position `i`, `1 ≤ i ≤ n - 1`
(the value `v` outside this range is never used). -/
def Ordering.pos {v : Fin n} (π : Ordering n v) (i : ℕ) : Fin n :=
  if h : i - 1 < n - 1 then (π ⟨i - 1, h⟩).1 else v

/-- `H_{-v} = {p ∈ ℝⁿ : p_v = 0, ∑_k p_k = 1}` (Brunck et al., Sec. 6). -/
def hyperplane (v : Fin n) : Set (Fin n → ℝ) :=
  {p | p v = 0 ∧ ∑ k, p k = 1}

/-- The partial sum `u_i = ∑_{j<i} p_{π_j}` over the positions `1 ≤ j < i`
(Brunck et al., Eq. (3)). -/
noncomputable def prefixSum {v : Fin n} (π : Ordering n v) (p : Fin n → ℝ) (i : ℕ) : ℝ :=
  ∑ j in Finset.Ico 1 i, p (π.pos j)

/-- The parallelepiped of Brunck et al., Sec. 7.1, Eq. (3): for `M ⊆ {2, …, n-1}`,
`B_{v,π,M} = {p ∈ H_{-v} : 0 ≤ u_i ≤ 1 (i ∈ M), -1 ≤ p_{π_i} ≤ 0 (i ∈ {2, …, n-1} ∖ M)}`. -/
def parallelepiped (v : Fin n) (π : Ordering n v) (M : Finset ℕ) : Set (Fin n → ℝ) :=
  {p | p ∈ hyperplane v ∧
    (∀ i ∈ M, 0 ≤ prefixSum π p i ∧ prefixSum π p i ≤ 1) ∧
    ∀ i ∈ Finset.Icc 2 (n - 1), i ∉ M → -1 ≤ p (π.pos i) ∧ p (π.pos i) ≤ 0}

/-- The paramid `pyr_{e_v}(B_{v,π,M})` of Brunck et al., Sec. 7.1 (Lemma 22). -/
def paramid (v : Fin n) (π : Ordering n v) (M : Finset ℕ) : Set (Fin n → ℝ) :=
  pyramid (Pi.single v 1) (parallelepiped v π M)

/-- Its support function `h_{pyr_{e_v}(B_{v,π,M})}`, the summand of their Lemma 22. -/
noncomputable def paramidSupport (v : Fin n) (π : Ordering n v) (M : Finset ℕ) :
    (Fin n → ℝ) → ℝ :=
  supportFunction (paramid v π M)

/-! ## The dictionary to caterpillar descriptions -/

/-- The last marked position `q = max ({1} ∪ M)`; for `M ≠ ∅` this is `max M`. -/
def lastMarked (M : Finset ℕ) : ℕ :=
  (insert 1 M).max' (Finset.insert_nonempty _ _)

/-- The marked parent `r(i) = max ({1} ∪ {j ∈ M : j < i})` of a position `i`. -/
def markedParent (M : Finset ℕ) (i : ℕ) : ℕ :=
  (insert 1 (M.filter fun j => j < i)).max' (Finset.insert_nonempty _ _)

/-- The word `(v, π₁, …, π_{r+1})` of an ordering, as a permutation of
`Fin (r + 2)` with apex `v` at position `0`. -/
noncomputable def Ordering.word {r : ℕ} {v : Fin (r + 1 + 1)} (π : Ordering (r + 1 + 1) v) :
    Equiv.Perm (Fin (r + 1 + 1)) :=
  Equiv.ofBijective (Fin.cases v fun i => (π i).1)
    (Finite.injective_iff_bijective.mp (by
      intro a b
      induction a using Fin.cases <;> induction b using Fin.cases <;> intro h
      · rfl
      · exact absurd h.symm (π _).2
      · exact absurd h (π _).2
      · exact congrArg Fin.succ (π.injective (Subtype.ext h))))

/-- The cut set `S = M - 1 = {j : j + 1 ∈ M}` of the caterpillar positions. -/
def cutSet {r : ℕ} (M : Finset ℕ) : Finset (Fin (r + 1)) :=
  Finset.univ.filter fun j => (j : ℕ) + 1 ∈ M

end BHRSY

end MaxCaterpillar
