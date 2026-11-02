import MaxCaterpillar.Frontier.StarCertificate.XiSelectors
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators
def maskSet (T : Fin 16) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => Nat.testBit T.val i.val = true)

def setMask (S : Finset (Fin 4)) : Fin 16 :=
  ⟨∑ i in S, 2 ^ i.val, by
    have h : (∑ i in S, 2 ^ i.val) ≤ ∑ i in (Finset.univ : Finset (Fin 4)), 2 ^ i.val :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun (i : Fin 4) _ _ => Nat.zero_le (2 ^ i.val))
    have hh : (∑ i in (Finset.univ : Finset (Fin 4)), 2 ^ i.val) = 15 := by decide
    rw [hh] at h
    exact Nat.lt_succ_of_le h⟩

theorem maskSet_setMask : ∀ S : Finset (Fin 4), maskSet (setMask S) = S := by decide

theorem setMask_maskSet : ∀ T : Fin 16, setMask (maskSet T) = T := by decide

def maskEquiv : Fin 16 ≃ Finset (Fin 4) where
  toFun := maskSet
  invFun := setMask
  left_inv := setMask_maskSet
  right_inv := maskSet_setMask


end MaxCaterpillar.Frontier.StarCertificate
