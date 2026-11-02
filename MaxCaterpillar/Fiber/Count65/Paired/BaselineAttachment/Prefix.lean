import MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment.Basic

set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment
open BigOperators Absorption

def prefixSlots (m r : ℕ) : Finset (Fin (m+r)) :=
  Finset.univ.map (Fin.castAddEmb r).toEmbedding

@[simp] theorem prefixSlots_card (m r : ℕ) : (prefixSlots m r).card=m := by
  simp [prefixSlots]

theorem prefixSlots_mem {m r : ℕ} (i : Fin m) : Fin.castAdd r i∈prefixSlots m r := by
  exact Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩

theorem prefixSlots_onto {m r : ℕ} (i : Fin (m+r)) (hi : i∈prefixSlots m r) :
    ∃ j : Fin m,Fin.castAdd r j=i := by
  rcases Finset.mem_map.mp hi with ⟨j,_hj,hj⟩
  exact ⟨j,hj⟩

theorem sum_prefixSlots {m r : ℕ} (f : Fin (m+r) → ℝ) :
    (∑ i in prefixSlots m r,f i)=∑ j : Fin m,f (Fin.castAdd r j) := by
  simp only [prefixSlots,Finset.sum_map]
  rfl

theorem appendSpectators_agree {N m k r : ℕ} (a b : Network N m k)
    (rows : Fin r → Fin m → ℝ) (bias weights : Fin r → ℝ)
    (hA : b.W₁=a.W₁) (hβ : b.b₁=a.b₁) (hθ : b.b₃=a.b₃) :
    AgreeOutside (appendSpectators a rows bias weights) (appendSpectators b rows bias weights)
      (prefixSlots k r) := by
  refine ⟨hA,hβ,hθ,?_⟩
  intro i
  refine Fin.addCases (fun j hi=>?_) (fun j _hi=>?_) i
  · exact False.elim (hi (prefixSlots_mem j))
  · simp [appendSpectators,Fin.append_right]

end MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment
