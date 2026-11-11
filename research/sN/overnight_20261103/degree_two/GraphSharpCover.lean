import research.sN.overnight_20261103.degree_two.GraphSharp
import research.sN.overnight_20261103.degree_two.CoverCounting

/-! Sharp graph capacity applied to a finite cover by original neuron indices.
The network localization supplying the cover remains a separate theorem. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.DegreeTwo
open BigOperators
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {J : Type*} [Fintype J]

/-- Integer form of the sharpened width count: no rounding loss is required. -/
theorem two_choose_le_card_mul_sharp_capacity (G : J→SimpleGraph (Fin N))
    (hdegree : ∀ j v, (G j).degree v≤2) (m : ℕ) (hm : 0<m)
    (hcover : ∀ S : Finset (Fin N), S.card=m →
      ∃ j, Nat.card ((G j).induce (S : Set (Fin N))).ConnectedComponent≤2) :
    2*N.choose m≤Fintype.card J*(2*N+(m-1)*N^2) := by
  calc
    2*N.choose m ≤ 2*∑ j, (twoComponentSets (G j) m).card :=
      Nat.mul_le_mul_left 2 (choose_le_sum_capacity G m hcover)
    _ = ∑ j, 2*(twoComponentSets (G j) m).card := Finset.mul_sum
    _ ≤ ∑ _j : J, (2*N+(m-1)*N^2) :=
      Finset.sum_le_sum (fun j _ => two_mul_twoComponentSets_card_le_sharp (G j) (hdegree j) m hm)
    _ = Fintype.card J*(2*N+(m-1)*N^2) := by
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]

#check @two_choose_le_card_mul_sharp_capacity
#print axioms two_choose_le_card_mul_sharp_capacity
end MaxCaterpillar.Overnight.DegreeTwo
