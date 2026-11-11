import MaxCaterpillar.Fiber.Count65.RootFrames
import MaxCaterpillar.Fiber.Count65.FourFeatures

/-! # From actual invariant rows to the finite coordinate-root classifier

Positive real scales and the chosen enumeration are transported explicitly.
The finite theorem is applied only after proving its necessary hypotheses from
all-input network exactness. No bounded coefficient alphabet is assumed.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65
open BigOperators MaxCaterpillar.Frontier
open RootFrames

/-- The four-root test applies after arbitrary positive rescaling of the
actual feature rows. -/
theorem scaled_root_frame_properties (A : Fin 4 → Point 4)
    (ell : Point 4) (Phi : (Fin 4 → ℝ) → ℝ)
    (hfactor : ∀ x, Maximum 4 x = lin ell x +
      Phi (fun j => relu (lin (A j) x)))
    (hcover : ∀ i, ∃ j, A j i = 0)
    (r : Fin 4 → Root) (s : Fin 4 → ℝ)
    (hloop : ∀ j, (r j).1 ≠ (r j).2) (hs : ∀ j, 0 < s j)
    (hrows : ∀ j, A j = s j • row (r j))
    (hdistinct : ∀ j k, j ≠ k → ∀ c : ℝ, 0 < c → A j ≠ c • A k) :
    (Finset.univ.image r).card = 4 ∧ NoLoops (Finset.univ.image r) ∧
      CoversTriples (Finset.univ.image r) ∧ Factors (Finset.univ.image r) := by
  classical
  let F : Frame := Finset.univ.image r
  have hinj : Function.Injective r := by
    intro j k hjk
    by_contra hne
    apply hdistinct j k hne (s j / s k) (div_pos (hs j) (hs k))
    rw [hrows j, hrows k, hjk, smul_smul, div_mul_cancel _ (hs k).ne']
  have hcard : F.card = 4 := by
    change (Finset.univ.image r).card = 4
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hnoloop : NoLoops F := by
    intro p hp
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hp
    exact hj ▸ hloop j
  have hcov : CoversTriples F := by
    intro i
    obtain ⟨j, hj⟩ := hcover i
    have hzero : row (r j) i = 0 := by
      rw [hrows j] at hj
      change s j * row (r j) i = 0 at hj
      exact (mul_eq_zero.mp hj).resolve_left (hs j).ne'
    obtain ⟨hi, hk⟩ := (row_zero_iff (r j) (hloop j) i).mp hzero
    exact ⟨r j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, hi.symm, hk.symm⟩
  have hf : Factors F := by
    let PhiRoot : (F → ℝ) → ℝ := fun z =>
      Phi (fun j => s j * z ⟨r j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩)
    refine ⟨ell, PhiRoot, ?_⟩
    intro x
    rw [hfactor]
    change lin ell x + Phi (fun j => relu (lin (A j) x)) =
      lin ell x + Phi (fun j => s j * relu (lin (row (r j)) x))
    congr 2
    funext j
    rw [hrows j, lin_smul_left, relu_mul_pos (hs j)]
  exact ⟨hcard, hnoloop, hcov, hf⟩

/-- Rootness is stated as a property of a genuine real first weight row. -/
def IsCoordinateRoot (a : Point 4) : Prop :=
  ∃ p : Root, p.1 ≠ p.2 ∧ ∃ c : ℝ, 0 < c ∧ a = c • row p

/-- Every actual network whose four invariant rows are coordinate roots has
one of the two exact finite first-root frames, with all row scales retained. -/
theorem network_four_invariant_root_data (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (invariantRows net).card = 4)
    (hroot : ∀ j, (∑ i, net.W₁ j i) = 0 → IsCoordinateRoot (net.W₁ j)) :
    ∃ e : Fin 4 ≃ invariantRows net,
      ∃ r : Fin 4 → Root, ∃ s : Fin 4 → ℝ,
        (∀ j, (r j).1 ≠ (r j).2) ∧ (∀ j, 0 < s j) ∧
        (∀ j, net.W₁ (e j).val = s j • row (r j)) ∧
        ((Finset.univ.image r).card = 4 ∧ NoLoops (Finset.univ.image r) ∧
          CoversTriples (Finset.univ.image r) ∧ Factors (Finset.univ.image r)) := by
  classical
  obtain ⟨e, ell, Phi, hf, _, _, _, hsum, hcover, _⟩ :=
    four_feature_factorization net hnet hcard
  have hr : ∀ j : Fin 4, ∃ p : Root, p.1 ≠ p.2 ∧
      ∃ c : ℝ, 0 < c ∧ net.W₁ (e j).val = c • row p :=
    fun j => hroot (e j).val (hsum j)
  choose r hloop s hs hrows using hr
  refine ⟨e, r, s, hloop, hs, hrows, ?_⟩
  apply scaled_root_frame_properties (fun j => net.W₁ (e j).val) ell Phi hf hcover
    r s hloop hs hrows
  intro j k hjk c hc
  apply net.first_rows_not_pos_proportional_of_max4_six hnet _ hc
  intro he
  exact hjk (e.injective (Subtype.ext he))

#print axioms scaled_root_frame_properties
#print axioms network_four_invariant_root_data
end MaxCaterpillar.Fiber.Count65
