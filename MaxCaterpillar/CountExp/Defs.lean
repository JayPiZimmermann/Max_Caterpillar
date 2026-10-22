import MaxCaterpillar.CountCubic.Structure
import MaxCaterpillar.Compilation
import Mathlib.LinearAlgebra.Pi

/-!
# Definitions for the exponential count of caterpillar face functions

Production definitions for the lower bound `C(N,k) ≤ 6^k |K|` (`research/sN/NOTE.md`,
"MAIN ROUTE").  Coordinates are `y_0, …, y_{N-1}` with `N = r + 2`; keys are read in
full coordinates through the API of `CountCubic.FullCoords`
(`keyHead`, `HasPair`, `kappa`, `pairSet`) and `CountCubic.Structure` (`HingeNbr`).

## Localities

A `k`-locality is encoded by a permutation `π` of the coordinates: `π o` is the
position of `o`.  The tie set is `T = {o : π o < k}` and the other coordinates are
ordered by their positions.  Every locality `(T, ρ)` with `|T| = k` arises from
exactly `k!` permutations, so counting permutations counts localities.

* `basePt k B π`: `0` on `T` and `-B^(π o)` at every other coordinate (step 1);
  a coordinate with a smaller position is higher.
* `boxPt k B δ π S`: the base point plus `δ` on `S ⊆ T`.
* `mixedDiff k B δ π`: the `k`-th mixed finite difference in the coordinates of `T`,
  `g ↦ ∑_{S ⊆ T} (-1)^{|T \ S|} g (boxPt S)`, as a linear functional.

## Pass conditions (step 2)

For an adjacency `adj` and values `κ`:
* `upCount adj π o`: number of `adj`-neighbours of `o` at a smaller position;
* `Balanced adj κ k π`: condition (a), every `o ∉ T` has exactly `κ_o` neighbours above;
* `Active adj κ k π`: condition (s), every `t ∈ T` with no neighbour in `T` has `κ_t ≠ 0`.
`Passes key k π` applies both to the functions `σ(y_i - y_j)` of the key
(`HingeNbr key`) and to `kappa key`.

## Path data (steps 5 and 6)

The hinge forest of a normalized key lies on a caterpillar: the spine vertices
`s 0, …, s q` in spine order, consecutive spine vertices joined by a hinge when the
index is in `links`, and pendant vertices `u` with `lp u = some i` joined only to
`s i` (`HingeCat`).  Positions with a pendant form `leafy`.  For a set `A` of spine
indices (the spine vertices in `T`), `matchCount` is the size of the greedy matching
of the step-5 order count: in every maximal run of `n` consecutive linked spine
vertices outside `A` it takes `⌊n/2⌋` spine edges, and a spine vertex outside `A`
with no link on either side takes one pendant edge.  `pathWeight` is the generating
function `∑_A 2^{-matchCount A} x^{|A|}` over the sets `A` that respect the forced
membership `F` of isolated spine vertices.
-/

open BigOperators Finset

namespace MaxCaterpillar.CountExp

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections MaxNN.ParamidGeom
  MaxNN.ParamidChain CountCubic

/-! ## Localities and the mixed finite difference -/

section Locality

variable {N : ℕ}

/-- The tie set `T = {o : π o < k}` of the locality of `π`. -/
def tieSet (k : ℕ) (π : Equiv.Perm (Fin N)) : Finset (Fin N) :=
  univ.filter fun o => ((π o : Fin N) : ℕ) < k

/-- The permutations whose tie set is `T`. -/
def fiber (k : ℕ) (T : Finset (Fin N)) : Finset (Equiv.Perm (Fin N)) :=
  univ.filter fun π => tieSet k π = T

/-- The integer base point of the locality: `0` on the tie set and `-B^(π o)`
at every other coordinate. -/
def basePt (k B : ℕ) (π : Equiv.Perm (Fin N)) (o : Fin N) : ℤ :=
  if ((π o : Fin N) : ℕ) < k then 0 else -((B : ℤ) ^ ((π o : Fin N) : ℕ))

/-- The base point as a real point. -/
noncomputable def basePtR (k B : ℕ) (π : Equiv.Perm (Fin N)) (o : Fin N) : ℝ :=
  (basePt k B π o : ℝ)

/-- A corner of the box of side `δ` at the base point: `δ` is added on `S`. -/
noncomputable def boxPt (k B : ℕ) (δ : ℝ) (π : Equiv.Perm (Fin N)) (S : Finset (Fin N))
    (o : Fin N) : ℝ :=
  basePtR k B π o + if o ∈ S then δ else 0

/-- The `k`-th mixed finite difference in the tie coordinates, at the base point,
with step `δ`: `g ↦ ∑_{S ⊆ T} (-1)^{|T \ S|} g (boxPt S)`. -/
noncomputable def mixedDiff (k B : ℕ) (δ : ℝ) (π : Equiv.Perm (Fin N)) :
    ((Fin N → ℝ) → ℝ) →ₗ[ℝ] ℝ :=
  ∑ S in (tieSet k π).powerset,
    ((-1 : ℝ) ^ (tieSet k π \ S).card) •
      LinearMap.proj (R := ℝ) (φ := fun _ : Fin N → ℝ => ℝ) (boxPt k B δ π S)

theorem mixedDiff_apply (k B : ℕ) (δ : ℝ) (π : Equiv.Perm (Fin N)) (g : (Fin N → ℝ) → ℝ) :
    mixedDiff k B δ π g =
      ∑ S in (tieSet k π).powerset, (-1 : ℝ) ^ (tieSet k π \ S).card * g (boxPt k B δ π S) := by
  unfold mixedDiff
  rw [LinearMap.coeFn_sum, Finset.sum_apply]
  rfl

end Locality

/-! ## The pass conditions -/

section Pass

variable {N : ℕ}

/-- The number of `adj`-neighbours of `o` at a smaller position (above `o`). -/
noncomputable def upCount (adj : Fin N → Fin N → Prop) (π : Equiv.Perm (Fin N)) (o : Fin N) :
    ℕ := by
  classical
  exact (univ.filter fun x => adj o x ∧ π x < π o).card

/-- Condition (a): every coordinate outside the tie set has exactly `κ_o`
neighbours above it. -/
def Balanced (adj : Fin N → Fin N → Prop) (κ : Fin N → ℝ) (k : ℕ) (π : Equiv.Perm (Fin N)) :
    Prop :=
  ∀ o, k ≤ ((π o : Fin N) : ℕ) → (upCount adj π o : ℝ) = κ o

/-- Condition (s): every tie coordinate without a neighbour in the tie set has
`κ_t ≠ 0`. -/
def Active (adj : Fin N → Fin N → Prop) (κ : Fin N → ℝ) (k : ℕ) (π : Equiv.Perm (Fin N)) :
    Prop :=
  ∀ t, ((π t : Fin N) : ℕ) < k → (∀ x, ((π x : Fin N) : ℕ) < k → ¬ adj t x) → κ t ≠ 0

variable {r : ℕ}

/-- The key passes the locality of `π`: conditions (a) and (s) for its functions
`σ(y_i - y_j)` and its values `κ`. -/
def Passes (key : RealKey (r + 1)) (k : ℕ) (π : Equiv.Perm (Fin (r + 1 + 1))) : Prop :=
  Balanced (HingeNbr key) (kappa key) k π ∧ Active (HingeNbr key) (kappa key) k π

/-- The permutations whose locality the key passes. -/
noncomputable def passSet (key : RealKey (r + 1)) (k : ℕ) :
    Finset (Equiv.Perm (Fin (r + 1 + 1))) := by
  classical
  exact univ.filter fun π => Passes key k π

end Pass

/-! ## Normalized keys in full coordinates

Three facts about normalized keys that both the functional and the digit
argument use. -/

section Keys

variable {r : ℕ}

/-- The head of a normalized key has integer full coordinates. -/
theorem keyHead_isInt {key : RealKey (r + 1)} (hkey : key ∈ normalizedKeys r)
    (o : Fin (r + 1 + 1)) : ∃ z : ℤ, keyHead key o = z := by
  classical
  obtain ⟨w, τ, rfl⟩ := exists_word_of_mem_normalizedKeys hkey
  rw [keyHead_wordFaceKey]
  have hind : ∀ a : Fin (r + 1 + 1), ∃ z : ℤ, (if a = o then (1 : ℝ) else 0) = z := by
    intro a
    split_ifs
    · exact ⟨1, by norm_num⟩
    · exact ⟨0, by norm_num⟩
  have hsum : ∀ (P : Fin r → Prop) [DecidablePred P] (f : Fin r → ℝ),
      (∀ j, ∃ z : ℤ, f j = z) → ∃ z : ℤ, (∑ j, if P j then f j else 0) = z := by
    intro P _ f hf
    choose g hg using hf
    exact ⟨∑ j, if P j then g j else 0, by push_cast; simp only [hg]⟩
  obtain ⟨a, ha⟩ := hind (lastV w)
  obtain ⟨b, hb⟩ := hind (apexV w)
  obtain ⟨c, hc⟩ := hsum (fun j => edgeState w τ j = 1)
    (fun j => (if parV w j = o then 1 else 0) - (if childV w j = o then 1 else 0))
    (fun j => by
      obtain ⟨x, hx⟩ := hind (parV w j)
      obtain ⟨y, hy⟩ := hind (childV w j)
      exact ⟨x - y, by dsimp only; rw [hx, hy]; push_cast; ring⟩)
  obtain ⟨d, hd⟩ := hsum (fun j => edgeState w τ j = 2 ∧ childV w j < parV w j)
    (fun j => (if parV w j = o then 1 else 0) - (if childV w j = o then 1 else 0))
    (fun j => by
      obtain ⟨x, hx⟩ := hind (parV w j)
      obtain ⟨y, hy⟩ := hind (childV w j)
      exact ⟨x - y, by dsimp only; rw [hx, hy]; push_cast; ring⟩)
  exact ⟨a - b + c + d, by rw [ha, hb, hc, hd]; push_cast; ring⟩

/-- A function `σ(y_i - y_j)` of a normalized key has `i < j`. -/
theorem hasPair_lt {key : RealKey (r + 1)} (hkey : key ∈ normalizedKeys r)
    {i j : Fin (r + 1 + 1)} (h : HasPair key i j) : i < j := by
  obtain ⟨p, hp, he⟩ := normalizedKey_label hkey h
  rw [mem_pairSet] at hp
  have hne : p.1 ≠ p.2 := ne_of_lt hp.1
  obtain ⟨h1, h2⟩ := simplex_difference_endpoints hne he.symm
  rw [← h1, ← h2]
  exact hp.1

/-- The preactivation of a normalized key in full coordinates:
`∑ₒ hₒ yₒ + ∑_{(i,j) ∈ M} σ(y_i - y_j)`. -/
theorem realUnitArg_eq {key : RealKey (r + 1)} (hkey : key ∈ normalizedKeys r)
    (y : Fin (r + 1 + 1) → ℝ) :
    realUnitArg key y =
      ∑ o, keyHead key o * y o + ∑ p in pairSet key, relu (y p.1 - y p.2) := by
  classical
  unfold realUnitArg
  rw [dot_coordT_eq_fullVec]
  congr 1
  have himg : key.2 = (pairSet key).image fun p => toR (vtx p.1) - toR (vtx p.2) := by
    ext v
    rw [Finset.mem_image]
    constructor
    · intro hv
      obtain ⟨p, hp, he⟩ := normalizedKey_label hkey hv
      exact ⟨p, hp, he.symm⟩
    · rintro ⟨p, hp, rfl⟩
      exact (mem_pairSet.mp hp).2
  rw [himg, Finset.sum_image]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [SupportCut.dot_sub_left, MaxNN.Width.dot_toR_vtx_coordT,
      MaxNN.Width.dot_toR_vtx_coordT]
    congr 1
    ring
  · intro p hp p' _ he
    have hne : p.1 ≠ p.2 := ne_of_lt (mem_pairSet.mp hp).1
    obtain ⟨h1, h2⟩ := simplex_difference_endpoints hne he
    exact Prod.ext h1 h2

end Keys

/-! ## Path data and the greedy matching -/

section Path

/-- The greedy matching on the spine: edge `i` (joining spine indices `i` and
`i + 1`) is chosen when it is a link, both ends are outside `A`, and edge `i - 1`
is not chosen. -/
def chosen (links A : Finset ℕ) : ℕ → Bool
  | 0 => decide (0 ∈ links ∧ 0 ∉ A ∧ 1 ∉ A)
  | i + 1 => decide (i + 1 ∈ links ∧ i + 1 ∉ A ∧ i + 2 ∉ A) && !chosen links A i

/-- Spine index `i` has no link on either side. -/
def Single (links : Finset ℕ) (i : ℕ) : Prop := (i = 0 ∨ i - 1 ∉ links) ∧ i ∉ links

instance (links : Finset ℕ) (i : ℕ) : Decidable (Single links i) := by
  unfold Single; infer_instance

/-- Spine index `i` is an isolated vertex of the hinge forest: no link and no pendant. -/
def IsoSpine (links leafy : Finset ℕ) (i : ℕ) : Prop := Single links i ∧ i ∉ leafy

instance (links leafy : Finset ℕ) (i : ℕ) : Decidable (IsoSpine links leafy i) := by
  unfold IsoSpine; infer_instance

/-- The size of the matching used in the step-5 order count: the greedy spine
edges, plus one pendant edge at every spine index outside `A` with no link on
either side and a pendant. -/
def matchCount (q : ℕ) (links leafy A : Finset ℕ) : ℕ :=
  ((range q).filter fun i => chosen links A i = true).card +
    ((range (q + 1)).filter fun i => Single links i ∧ i ∈ leafy ∧ i ∉ A).card

/-- The isolated spine indices `i ≤ q` are in `A` exactly when they are in `F`. -/
def RespectsForced (q : ℕ) (links leafy F A : Finset ℕ) : Prop :=
  ∀ i ∈ range (q + 1), IsoSpine links leafy i → (i ∈ A ↔ i ∈ F)

instance (q : ℕ) (links leafy F : Finset ℕ) : DecidablePred (RespectsForced q links leafy F) :=
  fun A => by unfold RespectsForced; infer_instance

/-- The admissible index sets: subsets of `{0, …, q}` whose isolated spine indices
are in `A` exactly when they are in `F`. -/
def admissibleIdx (q : ℕ) (links leafy F : Finset ℕ) : Finset (Finset ℕ) :=
  (range (q + 1)).powerset.filter (RespectsForced q links leafy F)

/-- The generating function `∑_A 2^{-matchCount A} x^{|A|}` of step 6. -/
def pathWeight (q : ℕ) (links leafy F : Finset ℕ) (x : ℚ) : ℚ :=
  ∑ A in admissibleIdx q links leafy F, (1 / 2 : ℚ) ^ matchCount q links leafy A * x ^ A.card

end Path

/-! ## Caterpillar hinge forests -/

/-- A hinge forest on a caterpillar: spine vertices `s 0, …, s q`, a link set
(`i ∈ links` joins `s i` and `s (i + 1)`), and the pendant vertices `u` with
`lp u = some i`, joined to `s i`.  All other vertices are isolated. -/
structure HingeCat (N : ℕ) where
  q : ℕ
  s : ℕ → Fin N
  links : Finset ℕ
  lp : Fin N → Option ℕ

namespace HingeCat

variable {N : ℕ} (H : HingeCat N)

/-- The spine indices that carry a pendant vertex. -/
def leafy : Finset ℕ := (range (H.q + 1)).filter fun i => ∃ u, H.lp u = some i

/-- `o` is a spine vertex. -/
def OnSpine (o : Fin N) : Prop := ∃ i ∈ range (H.q + 1), H.s i = o

/-- The adjacency of the hinge forest. -/
def Adj (u v : Fin N) : Prop :=
  (∃ i ∈ H.links, (u = H.s i ∧ v = H.s (i + 1)) ∨ (u = H.s (i + 1) ∧ v = H.s i)) ∨
    (∃ i, H.lp u = some i ∧ v = H.s i) ∨ (∃ i, H.lp v = some i ∧ u = H.s i)

/-- Well-formedness: the spine is injective, links join spine indices `≤ q`, and
pendant vertices hang off spine indices `≤ q` and are not spine vertices. -/
structure WF : Prop where
  s_inj : ∀ i ≤ H.q, ∀ j ≤ H.q, H.s i = H.s j → i = j
  links_sub : H.links ⊆ range H.q
  lp_le : ∀ u i, H.lp u = some i → i ≤ H.q
  lp_not_spine : ∀ u i, H.lp u = some i → ¬ H.OnSpine u

/-- The spine indices whose vertex lies in `T`. -/
def spineIdx (T : Finset (Fin N)) : Finset ℕ := (range (H.q + 1)).filter fun i => H.s i ∈ T

/-- The spine indices whose vertex has `κ ≠ 0`. -/
noncomputable def forcedIdx (κ : Fin N → ℝ) : Finset ℕ := by
  classical
  exact (range (H.q + 1)).filter fun i => κ (H.s i) ≠ 0

/-- Step 4: the shape of a tie set passed by a key.  A pendant vertex is in `T`
exactly with its spine vertex; an isolated spine vertex and every vertex off the
caterpillar forest is in `T` exactly when `κ ≠ 0`. -/
def Admissible (κ : Fin N → ℝ) (T : Finset (Fin N)) : Prop :=
  (∀ u i, H.lp u = some i → (u ∈ T ↔ H.s i ∈ T)) ∧
    (∀ i ≤ H.q, IsoSpine H.links H.leafy i → (H.s i ∈ T ↔ κ (H.s i) ≠ 0)) ∧
    (∀ o, ¬ H.OnSpine o → H.lp o = none → (o ∈ T ↔ κ o ≠ 0))

end HingeCat

end MaxCaterpillar.CountExp
