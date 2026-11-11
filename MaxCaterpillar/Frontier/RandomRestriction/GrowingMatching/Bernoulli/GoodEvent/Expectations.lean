import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Association

/-! # Finite conditional expectation identities for actual Bernoulli subsets

These algebraic helpers do not impose a probability estimate on an event.
Conditioning-set monotonicity is needed only when invoking the separately
proved Harris domination for selected-label indicators.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
open BigOperators
variable {n : ℕ}

theorem condMean_mono_on {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hpos : 0<mass p D)
    {f g : Finset (Fin n)→ℝ} (hfg : ∀ S∈D,f S≤g S) :
    condMean p D f≤condMean p D g := by
  unfold condMean
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum fun S hS =>
      mul_le_mul_of_nonneg_left (hfg S hS) (weight_nonneg hp0 hp1 S)
  · exact (inv_pos.mpr hpos).le

theorem condMean_const {p : ℝ} (D : Finset (Finset (Fin n)))
    (hpos : 0<mass p D) (c : ℝ) : condMean p D (fun _=>c)=c := by
  unfold condMean
  rw [←Finset.sum_mul]
  change (mass p D)⁻¹*(mass p D*c)=c
  rw [←mul_assoc,inv_mul_cancel hpos.ne',one_mul]

theorem condMean_add (p : ℝ) (D : Finset (Finset (Fin n)))
    (f g : Finset (Fin n)→ℝ) :
    condMean p D (fun S=>f S+g S)=condMean p D f+condMean p D g := by
  unfold condMean
  simp only [mul_add,Finset.sum_add_distrib]

theorem condMean_const_mul (p : ℝ) (D : Finset (Finset (Fin n)))
    (c : ℝ) (f : Finset (Fin n)→ℝ) :
    condMean p D (fun S=>c*f S)=c*condMean p D f := by
  have hs : (∑ S in D,weight p S*(c*f S))=c*∑ S in D,weight p S*f S := by
    calc
      _ = ∑ S in D,c*(weight p S*f S) :=
        Finset.sum_congr rfl (fun S _ => by ring)
      _ = _ := by rw [Finset.mul_sum]
  unfold condMean
  rw [hs]
  ring

theorem condMean_sum {ι : Type*} [Fintype ι] (p : ℝ)
    (D : Finset (Finset (Fin n))) (f : ι→Finset (Fin n)→ℝ) :
    condMean p D (fun S=>∑ i,f i S)=∑ i,condMean p D (f i) := by
  unfold condMean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem condMean_le_const {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hpos : 0<mass p D)
    (f : Finset (Fin n)→ℝ) (c : ℝ) (hf : ∀ S∈D,f S≤c) :
    condMean p D f≤c :=
  (condMean_mono_on hp0 hp1 D hpos hf).trans_eq (condMean_const D hpos c)

/-- A fixed original label has conditional inclusion probability at most p. -/
theorem condMean_mem_le {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0<mass p D) (i : Fin n) :
    condMean p D (fun S=>if i∈S then (1:ℝ) else 0)≤p := by
  simpa only [Finset.singleton_subset_iff,Finset.card_singleton,pow_one] using
    condMean_contains_le hp0 hp1 D hD hpos ({i} : Finset (Fin n))

/-- Any fixed pair of distinct original labels has inclusion probability at most p². -/
theorem condMean_pair_subset_le {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0<mass p D) (I : Finset (Fin n)) (hI : I.card=2) :
    condMean p D (fun S=>if I⊆S then (1:ℝ) else 0)≤p^2 := by
  simpa only [hI] using condMean_contains_le hp0 hp1 D hD hpos I

#print axioms condMean_mono_on
#print axioms condMean_sum
#print axioms condMean_mem_le
#print axioms condMean_pair_subset_le
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
