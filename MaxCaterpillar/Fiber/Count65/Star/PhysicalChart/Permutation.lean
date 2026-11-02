import MaxCaterpillar.Fiber.Count65.Star.PhysicalNormalForm

/-! # Canonical core/head order is a genuine physical hidden permutation -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.Star.PhysicalChart
open MaxCaterpillar.Frontier

private theorem five_index_equiv (c l r u v : Fin 5)
    (hcl : c≠l) (hcr : c≠r) (hcu : c≠u) (hcv : c≠v)
    (hlr : l≠r) (hlu : l≠u) (hlv : l≠v) (hru : r≠u) (hrv : r≠v) (huv : u≠v) :
    ∃ e : Equiv.Perm (Fin 5), e 0=c ∧ e 1=l ∧ e 2=r ∧ e 3=u ∧ e 4=v := by
  let f : Fin 5→Fin 5 := ![c,l,r,u,v]
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [f,hcl,hcr,hcu,hcv,hlr,hlu,hlv,hru,hrv,huv,
        Ne.symm hcl,Ne.symm hcr,Ne.symm hcu,Ne.symm hcv,Ne.symm hlr,
        Ne.symm hlu,Ne.symm hlv,Ne.symm hru,Ne.symm hrv,Ne.symm huv]
  exact ⟨Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,rfl⟩),rfl,rfl,rfl,rfl,rfl⟩

lemma coreIndices_ne_heads {p n : Fin 5} (i : coreIndices p n) : i.val≠p ∧ i.val≠n := by
  have hi := Finset.mem_erase.mp i.property
  exact ⟨(Finset.mem_erase.mp hi.2).1,hi.1⟩

/-- Every actual derived role order extends to the original five neurons. -/
theorem exists_normalFormPermutation {net : Network 4 6 5} {r : ℝ}
    (F : PhysicalNormalForm net r) :
    ∃ e : Equiv.Perm (Fin 5),
      e 0=(F.order 0).val ∧ e 1=(F.order 1).val ∧ e 2=(F.order 2).val ∧
      e 3=F.positiveHead ∧ e 4=F.negativeHead := by
  have hi {i j : Fin 3} (h : i≠j) : (F.order i).val≠(F.order j).val := by
    intro he
    exact h (F.order.injective (Subtype.ext he))
  have h0 := coreIndices_ne_heads (F.order 0)
  have h1 := coreIndices_ne_heads (F.order 1)
  have h2 := coreIndices_ne_heads (F.order 2)
  exact five_index_equiv _ _ _ _ _ (hi (by decide)) (hi (by decide)) h0.1 h0.2
    (hi (by decide)) h1.1 h1.2 h2.1 h2.2 F.heads_distinct

noncomputable def normalFormPermutation {net : Network 4 6 5} {r : ℝ}
    (F : PhysicalNormalForm net r) : Equiv.Perm (Fin 5) :=
  Classical.choose (exists_normalFormPermutation F)

lemma normalFormPermutation_spec {net : Network 4 6 5} {r : ℝ}
    (F : PhysicalNormalForm net r) :
    normalFormPermutation F 0=(F.order 0).val ∧
    normalFormPermutation F 1=(F.order 1).val ∧
    normalFormPermutation F 2=(F.order 2).val ∧
    normalFormPermutation F 3=F.positiveHead ∧
    normalFormPermutation F 4=F.negativeHead :=
  Classical.choose_spec (exists_normalFormPermutation F)

/-- This reordering is literally the original physical hidden-permutation action. -/
noncomputable def orderedPhysicalNet {net : Network 4 6 5} {r : ℝ}
    (F : PhysicalNormalForm net r) : Network 4 6 5 :=
  permuteHidden net.zeroBias (Equiv.refl _) (normalFormPermutation F)

lemma orderedPhysicalNet_zeroBiases {net : Network 4 6 5} {r : ℝ}
    (F : PhysicalNormalForm net r) : (orderedPhysicalNet F).HasZeroBiases := by
  exact ⟨rfl,rfl,rfl⟩
end MaxCaterpillar.Fiber.Count65.Star.PhysicalChart
