import research.sN.max5_optimal_20261103.lower.unrestricted_four.convex_general.Simplex
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.TiedMaximum

/-! Exact MAX germs at translated contact vertices. -/
set_option autoImplicit false

namespace MaxCaterpillar.Max5Optimal.ConvexCores
open BigOperators Filter Topology Frontier
open Frontier.RandomRestriction.NormalizedNetwork

variable {N m n : ℕ}

def omitEmbedding (i : Fin (n+1)) : Fin n ↪ Fin (n+1) :=
  (Fin.succAboveEmb i).toEmbedding

@[simp] theorem omitEmbedding_apply (i : Fin (n+1)) (j : Fin n) :
    omitEmbedding i j = i.succAbove j := rfl

theorem omitEmbedding_ne (i : Fin (n+1)) (j : Fin n) :
    omitEmbedding i j ≠ i := Fin.succAbove_ne i j

theorem eq_of_not_mem_omitEmbedding (i j : Fin (n+1))
    (hj : j ∉ Finset.univ.image (omitEmbedding i)) : j = i := by
  classical
  by_contra h
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq h
  exact hj (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)

@[simp] theorem contactVertex_selected (M s : ℝ) (i : Fin (n+1)) (j : Fin n) :
    contactVertex M s i (omitEmbedding i j) = M :=
  contactVertex_other M s i _ (omitEmbedding_ne i j)

theorem contactVertex_outside (M s : ℝ) (i j : Fin (n+1))
    (hj : j ∉ Finset.univ.image (omitEmbedding i)) :
    contactVertex M s i j = M - s := by
  rw [eq_of_not_mem_omitEmbedding i j hj, contactVertex_self]

theorem tied_Maximum_eq_level [NeZero N] [NeZero m]
    (e : Fin m ↪ Fin N) (q : Point N) (M : ℝ)
    (hq : ∀ a, q (e a) = M)
    (hneg : ∀ i, i ∉ Finset.univ.image e → q i < M) :
    Maximum N q = M := by
  classical
  apply Maximum_eq_of q M (e 0) (hq 0)
  intro i
  by_cases hi : i ∈ Finset.univ.image e
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
    rw [hq a]
  · exact (hneg i hi).le

theorem eventually_tied_Maximum_at_level [NeZero N] [NeZero m]
    (e : Fin m ↪ Fin N) (q : Point N) (M : ℝ)
    (hq : ∀ a, q (e a) = M)
    (hneg : ∀ i, i ∉ Finset.univ.image e → q i < M) (x : Point m) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Maximum N (q + ε • lift e x) = M + ε * Maximum m x := by
  let q₀ : Point N := fun i => q i - M
  have hq₀ : ∀ a, q₀ (e a) = 0 := by
    intro a
    simp only [q₀, hq a, sub_self]
  have hn₀ : ∀ i, i ∉ Finset.univ.image e → q₀ i < 0 := by
    intro i hi
    exact sub_neg.mpr (hneg i hi)
  have heq (ε : ℝ) : q + ε • lift e x = (q₀ + ε • lift e x) + diag M := by
    funext i
    simp only [Pi.add_apply, q₀, diag]
    ring
  filter_upwards [eventually_tied_Maximum e q₀ hq₀ hn₀ x] with ε hε
  rw [heq ε, Maximum_add_diag, hε]
  ring

theorem contactVertex_Maximum [NeZero n] (M s : ℝ) (hs : 0 < s)
    (i : Fin (n+1)) : Maximum (n+1) (contactVertex M s i) = M := by
  apply tied_Maximum_eq_level (omitEmbedding i) _ M (contactVertex_selected M s i)
  intro j hj
  rw [contactVertex_outside M s i j hj]
  linarith only [hs]

theorem eventually_contactVertex_Maximum [NeZero n] (M s : ℝ) (hs : 0 < s)
    (i : Fin (n+1)) (x : Point n) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Maximum (n+1) (contactVertex M s i + ε • lift (omitEmbedding i) x) =
        M + ε * Maximum n x := by
  apply eventually_tied_Maximum_at_level (omitEmbedding i) _ M
    (contactVertex_selected M s i) _ x
  intro j hj
  rw [contactVertex_outside M s i j hj]
  linarith only [hs]

#check @tied_Maximum_eq_level
#check @eventually_tied_Maximum_at_level
#print axioms tied_Maximum_eq_level
#print axioms eventually_tied_Maximum_at_level
#print axioms contactVertex_Maximum
#print axioms eventually_contactVertex_Maximum

end MaxCaterpillar.Max5Optimal.ConvexCores
