import MaxCaterpillar.Fiber.First65.Irredundancy

/-! # Positive ray coverage produces a genuine row permutation

No ordering of the original rows is assumed. Irredundancy forces any choice
of a target ray for each source row to be injective, hence bijective.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.FrameTransport
open MaxCaterpillar.Frontier

theorem positive_ray_matching {n : ℕ} (A B : Fin n → Point 4)
    (hdistinct : ∀ j k, j≠k → ∀ c : ℝ,0<c → A j≠c • A k)
    (hcover : ∀ j,∃ k : Fin n,∃ c : ℝ,0<c ∧ A j=c • B k) :
    ∃ p : Equiv.Perm (Fin n),∃ s : Fin n→ℝ,
      (∀ j,0<s j) ∧ ∀ j,A j=s j • B (p j) := by
  classical
  choose k s hs hrows using hcover
  have hinj : Function.Injective k := by
    intro j l he
    by_contra hne
    apply hdistinct j l hne (s j/s l) (div_pos (hs j) (hs l))
    rw [hrows j,hrows l,he,smul_smul,div_mul_cancel _ (hs l).ne']
  exact ⟨Equiv.ofBijective k ⟨hinj,Finite.surjective_of_injective hinj⟩,s,hs,hrows⟩

/-- Actual exact width-six networks need no extra irredundancy premise. -/
theorem network_first_matrix_of_positive_ray_cover {h₂ : ℕ}
    (net : Network 4 6 h₂) (hnet : ∀ x,net.eval x=Maximum 4 x)
    (B : Fin 6→Point 4)
    (hcover : ∀ j,∃ k : Fin 6,∃ c : ℝ,0<c ∧ net.W₁ j=c • B k) :
    ∃ p : Equiv.Perm (Fin 6),∃ s : Fin 6→ℝ,
      (∀ j,0<s j) ∧ ∀ j,net.W₁ j=s j • B (p j) := by
  apply positive_ray_matching net.W₁ B _ hcover
  intro j k hjk c hc
  exact net.first_rows_not_pos_proportional_of_max4_six hnet hjk hc

#print axioms positive_ray_matching
#print axioms network_first_matrix_of_positive_ray_cover
end MaxCaterpillar.Fiber.Count65.FrameTransport
