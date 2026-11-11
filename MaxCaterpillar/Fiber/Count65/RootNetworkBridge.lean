import MaxCaterpillar.Fiber.Count65.RootFrameClassification
import MaxCaterpillar.Fiber.Count65.RootNetworkData
import MaxCaterpillar.Fiber.Count65.RootNormalization

set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65
open BigOperators MaxCaterpillar.Frontier RootFrames

/-- The four invariant rows of an actual network, with their exact real scales,
have either the paired-wall or the star-endpoint directed root graph. -/
theorem network_four_invariant_root_frame (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (invariantRows net).card = 4)
    (hroot : ∀ j, (∑ i, net.W₁ j i) = 0 → IsCoordinateRoot (net.W₁ j)) :
    ∃ e : Fin 4 ≃ invariantRows net,
      ∃ r : Fin 4 → Root, ∃ s : Fin 4 → ℝ,
        (∀ j, (r j).1 ≠ (r j).2) ∧ (∀ j, 0 < s j) ∧
        (∀ j, net.W₁ (e j).val = s j • row (r j)) ∧
        NormalForm (Finset.univ.image r) := by
  obtain ⟨e,r,s,hl,hs,hr,hc,hn,hcov,hf⟩ :=
    network_four_invariant_root_data net hnet hcard hroot
  exact ⟨e,r,s,hl,hs,hr, four_roots_normal_form _ hc hn hcov hf⟩

/-- The same classification stated directly using the support sizes of actual
first weight rows. Arbitrary real magnitudes and all biases are allowed. -/
theorem network_four_support_two_frame (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (invariantRows net).card = 4)
    (hroot : ∀ j, (∑ i, net.W₁ j i) = 0 →
      (nonzeroCoordinates (net.W₁ j)).card = 2) :
    ∃ e : Fin 4 ≃ invariantRows net,
      ∃ r : Fin 4 → Root, ∃ s : Fin 4 → ℝ,
        (∀ j, (r j).1 ≠ (r j).2) ∧ (∀ j, 0 < s j) ∧
        (∀ j, net.W₁ (e j).val = s j • row (r j)) ∧
        NormalForm (Finset.univ.image r) := by
  apply network_four_invariant_root_frame net hnet hcard
  intro j hj
  exact positive_root_of_support_two _ hj (hroot j hj)

/-- Physical directions for the two surviving four-root frames. This version
is convenient for carrier completion and has no chosen row enumeration in
its conclusion. -/
theorem network_four_root_directions (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (invariantRows net).card = 4)
    (hroot : ∀ j, (∑ i, net.W₁ j i) = 0 →
      (nonzeroCoordinates (net.W₁ j)).card = 2) :
    ∃ q : Equiv.Perm (Fin 4),
      (∀ j, (∑ i, net.W₁ j i) = 0 →
        ∃ a ∈ pairedFrame q, ∃ c : ℝ, 0 < c ∧ net.W₁ j = c • row a) ∨
      (∀ j, (∑ i, net.W₁ j i) = 0 →
        ∃ a ∈ starFrame q, ∃ c : ℝ, 0 < c ∧ net.W₁ j = c • row a) := by
  classical
  obtain ⟨e,r,s,hl,hs,hr,p,hp,hpF⟩ :=
    network_four_support_two_frame net hnet hcard hroot
  let q : Equiv.Perm (Fin 4) :=
    Equiv.ofBijective p ⟨hp, Finite.surjective_of_injective hp⟩
  have hcover : ∀ j, (∑ i, net.W₁ j i) = 0 →
      ∃ a ∈ Finset.univ.image r, ∃ c : ℝ, 0 < c ∧ net.W₁ j = c • row a := by
    intro j hj
    have hjm : j ∈ invariantRows net := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
    obtain ⟨k,hk⟩ := e.surjective ⟨j,hjm⟩
    have hkv : (e k).val = j := congrArg Subtype.val hk
    refine ⟨r k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _,rfl⟩,s k,hs k,?_⟩
    rw [← hkv]
    exact hr k
  refine ⟨q, ?_⟩
  rcases hpF with hpaired | hstar
  · left
    simpa only [hpaired] using hcover
  · right
    simpa only [hstar] using hcover

#print axioms network_four_support_two_frame
#print axioms network_four_root_directions
end MaxCaterpillar.Fiber.Count65
