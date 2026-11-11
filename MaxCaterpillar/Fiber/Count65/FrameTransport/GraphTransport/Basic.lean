import MaxCaterpillar.Fiber.Count65.FrameTransport.NormalizedFeatureFrame
import MaxCaterpillar.Fiber.Count65.FrameTransport.RayMatching
import MaxCaterpillar.Fiber.Count65.SmallRootFrames

/-! # Transport a finite root frame to arbitrary real feature rows

The graph equality is used only to locate each oriented root. Complement
indices select the actual nonroot rows, and irredundancy forces the resulting
positive-ray assignment to be a genuine permutation of all four observations.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.FrameTransport
open MaxCaterpillar.Frontier BigOperators TwoRoots RootFrames SmallRootFrames

noncomputable def twoGraphRows (C : Fin 2 → Root) (s t : Point 4) : Fin 4 → Point 4 :=
  ![row (C 0),row (C 1),s,t]

noncomputable def threeGraphRows (C : Fin 3 → Root) (t : Point 4) : Fin 4 → Point 4 :=
  ![row (C 0),row (C 1),row (C 2),t]

theorem row_relabel (q : Equiv.Perm (Fin 4)) (r : Root) :
    row (q r.1,q r.2) = fun i => row r (q.symm i) := by
  funext i
  have h₁ : i=q r.1 ↔ q.symm i=r.1 := by
    constructor
    · intro h; rw [h,q.symm_apply_apply]
    · intro h; rw [←h,q.apply_symm_apply]
  have h₂ : i=q r.2 ↔ q.symm i=r.2 := by
    constructor
    · intro h; rw [h,q.symm_apply_apply]
    · intro h; rw [←h,q.apply_symm_apply]
  simp only [row,h₁,h₂]

theorem threeGraphRows_root (C : Fin 3 → Root) (t : Point 4) (j : Fin 3) :
    threeGraphRows C t (Fin.castAdd 1 j) = row (C j) := by
  fin_cases j <;> rfl

theorem twoGraphRows_root (C : Fin 2 → Root) (s t : Point 4) (j : Fin 2) :
    twoGraphRows C s t (Fin.castAdd 2 j) = row (C j) := by
  fin_cases j <;> rfl

private theorem root_located {A : Fin 4 → Point 4} (nf : NormalizedFeatureFrame A)
    {m : ℕ} (C : Fin m → Root) (q : Equiv.Perm (Fin 4))
    (hframe : (rootIndices A).image nf.roots = relabel q (Finset.univ.image C))
    (j : Fin 4) (hj : j ∈ rootIndices A) :
    ∃ l : Fin m, nf.rows j = fun i => row (C l) (q.symm i) := by
  have hm : nf.roots j ∈ (rootIndices A).image nf.roots :=
    Finset.mem_image.mpr ⟨j,hj,rfl⟩
  rw [hframe] at hm
  obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hm
  obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hr
  refine ⟨l,?_⟩
  rw [nf.root_row j hj,←he,←hl]
  exact row_relabel q (C l)

/-- With exactly three roots, the unique complementary row is selected
from the original normalized dictionary and transported by the input labels. -/
theorem normalize_three_graph {A : Fin 4 → Point 4} (nf : NormalizedFeatureFrame A)
    (hprop : ∀ j k,j≠k → ∀ c : ℝ,0<c → A j≠c • A k)
    (hc : (rootIndices A).card=3) (C : Fin 3 → Root) (q : Equiv.Perm (Fin 4))
    (hframe : (rootIndices A).image nf.roots = relabel q (Finset.univ.image C)) :
    ∃ t : Point 4,(∑ i,t i=0) ∧ Nonroot t ∧
      ∃ p : Equiv.Perm (Fin 4),∃ s : Fin 4→ℝ,(∀ j,0<s j) ∧
        ∀ j,A j=s j • (fun i => threeGraphRows C t (p j) (q.symm i)) := by
  classical
  have hadd : (rootIndices A).card+(rootIndices A)ᶜ.card=4 := by
    simpa using (rootIndices A).card_add_card_compl
  have hcomp : (rootIndices A)ᶜ.card=1 := by linarith only [hadd,hc]
  obtain ⟨u,hu⟩ := Finset.card_eq_one.mp hcomp
  have hun : u∉rootIndices A := by
    apply Finset.mem_compl.mp
    rw [hu]
    exact Finset.mem_singleton_self u
  have hcomplement (j : Fin 4) (hj : j∉rootIndices A) : j=u := by
    have hm := Finset.mem_compl.mpr hj
    rw [hu] at hm
    exact Finset.mem_singleton.mp hm
  let t : Point 4 := fun i => nf.rows u (q i)
  refine ⟨t,?_,nonroot_permute (nf.rows u) q (nf.nonroot u hun),?_⟩
  · exact (sum_permute (nf.rows u) q).trans (nf.sum_zero u)
  · apply positive_ray_matching A (fun j i => threeGraphRows C t j (q.symm i)) hprop
    intro j
    by_cases hj : j∈rootIndices A
    · obtain ⟨l,hl⟩ := root_located nf C q hframe j hj
      refine ⟨Fin.castAdd 1 l,nf.scales j,nf.positive j,?_⟩
      rw [nf.factorization j,threeGraphRows_root,hl]
    · have he := hcomplement j hj
      subst j
      refine ⟨3,nf.scales u,nf.positive u,?_⟩
      rw [nf.factorization u]
      congr 1
      funext i
      change nf.rows u i = nf.rows u (q (q.symm i))
      rw [q.apply_symm_apply]

/-- With exactly two roots, the two complementary rows are selected from
the actual dictionary before any canonical row ordering is imposed. -/
theorem normalize_two_graph {A : Fin 4 → Point 4} (nf : NormalizedFeatureFrame A)
    (hprop : ∀ j k,j≠k → ∀ c : ℝ,0<c → A j≠c • A k)
    (hc : (rootIndices A).card=2) (C : Fin 2 → Root) (q : Equiv.Perm (Fin 4))
    (hframe : (rootIndices A).image nf.roots = relabel q (Finset.univ.image C)) :
    ∃ s t : Point 4,(∑ i,s i=0) ∧ (∑ i,t i=0) ∧ Nonroot s ∧ Nonroot t ∧
      ∃ p : Equiv.Perm (Fin 4),∃ c : Fin 4→ℝ,(∀ j,0<c j) ∧
        ∀ j,A j=c j • (fun i => twoGraphRows C s t (p j) (q.symm i)) := by
  classical
  have hadd : (rootIndices A).card+(rootIndices A)ᶜ.card=4 := by
    simpa using (rootIndices A).card_add_card_compl
  have hcomp : (rootIndices A)ᶜ.card=2 := by linarith only [hadd,hc]
  obtain ⟨u,v,huv,hcompuv⟩ := Finset.card_eq_two.mp hcomp
  have hun : u∉rootIndices A := by
    apply Finset.mem_compl.mp
    rw [hcompuv]
    simp
  have hvn : v∉rootIndices A := by
    apply Finset.mem_compl.mp
    rw [hcompuv]
    simp
  have hcomplement (j : Fin 4) (hj : j∉rootIndices A) : j=u ∨ j=v := by
    have hm := Finset.mem_compl.mpr hj
    rw [hcompuv] at hm
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
  let s : Point 4 := fun i => nf.rows u (q i)
  let t : Point 4 := fun i => nf.rows v (q i)
  refine ⟨s,t,(sum_permute (nf.rows u) q).trans (nf.sum_zero u),
    (sum_permute (nf.rows v) q).trans (nf.sum_zero v),
    nonroot_permute (nf.rows u) q (nf.nonroot u hun),
    nonroot_permute (nf.rows v) q (nf.nonroot v hvn),?_⟩
  apply positive_ray_matching A (fun j i => twoGraphRows C s t j (q.symm i)) hprop
  intro j
  by_cases hj : j∈rootIndices A
  · obtain ⟨l,hl⟩ := root_located nf C q hframe j hj
    refine ⟨Fin.castAdd 2 l,nf.scales j,nf.positive j,?_⟩
    rw [nf.factorization j,twoGraphRows_root,hl]
  · rcases hcomplement j hj with he | he
    · subst j
      refine ⟨2,nf.scales u,nf.positive u,?_⟩
      rw [nf.factorization u]
      congr 1
      funext i
      change nf.rows u i = nf.rows u (q (q.symm i))
      rw [q.apply_symm_apply]
    · subst j
      refine ⟨3,nf.scales v,nf.positive v,?_⟩
      rw [nf.factorization v]
      congr 1
      funext i
      change nf.rows v i = nf.rows v (q (q.symm i))
      rw [q.apply_symm_apply]

#print axioms normalize_three_graph
#print axioms normalize_two_graph
end MaxCaterpillar.Fiber.Count65.FrameTransport
