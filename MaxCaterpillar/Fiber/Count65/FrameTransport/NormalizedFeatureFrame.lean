import MaxCaterpillar.Fiber.Count65.FrameTransport.FeatureNormalization
import MaxCaterpillar.Fiber.Count65.FrameTransport.RootSelection

/-! # Normalize exactly the actual two-support rows

The selection is the support-defined `rootIndices A`, not an assumed root
classification. Every selected row receives its own positive real scale.
The other rows are unchanged and are proved to be genuine nonroots.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.FrameTransport
open MaxCaterpillar.Frontier BigOperators TwoRoots

/-- An explicit normalized dictionary, with its genuine oriented root frame
and all of the original maximum-representation constraints retained. -/
structure NormalizedFeatureFrame (A : Fin 4 → Point 4) where
  rows : Fin 4 → Point 4
  scales : Fin 4 → ℝ
  roots : Fin 4 → RootFrames.Root
  positive : ∀ j, 0 < scales j
  factorization : ∀ j, A j = scales j • rows j
  root_proper : ∀ j ∈ rootIndices A, (roots j).1 ≠ (roots j).2
  root_row : ∀ j ∈ rootIndices A, rows j = RootFrames.row (roots j)
  nonroot : ∀ j, j ∉ rootIndices A → Nonroot (rows j)
  root_injective : Set.InjOn roots (rootIndices A)
  root_frame_card : ((rootIndices A).image roots).card = (rootIndices A).card
  root_frame_noLoops : RootFrames.NoLoops ((rootIndices A).image roots)
  sum_zero : ∀ j, ∑ i, rows j i = 0
  row_nonzero : ∀ j, rows j ≠ 0
  represents : Represents rows
  cover : ∀ i, ∃ j, rows j i = 0

/-- Every irredundant zero-sum four-feature representation has such a frame.
No graph type, row order, fourth-root condition, or finite coefficient
alphabet is assumed. -/
theorem normalized_feature_frame_exists (A : Fin 4 → Point 4)
    (hsum : ∀ j, ∑ i, A j i = 0) (hne : ∀ j, A j ≠ 0)
    (hprop : ∀ j k, j ≠ k → ∀ c : ℝ, 0 < c → A j ≠ c • A k)
    (hrep : Represents A) (hcover : ∀ i, ∃ j, A j i = 0) :
    Nonempty (NormalizedFeatureFrame A) := by
  classical
  have hchoose (j : Fin 4) :
      ∃ (B : Point 4) (s : ℝ) (r : RootFrames.Root),
        0 < s ∧ A j = s • B ∧
        (j ∈ rootIndices A → r.1 ≠ r.2 ∧ B = RootFrames.row r) ∧
        (j ∉ rootIndices A → Nonroot B) := by
    by_cases hj : j ∈ rootIndices A
    · obtain ⟨r,hr,s,hs,he⟩ := positive_root_of_support_two (A j) (hsum j)
        ((mem_rootIndices A j).mp hj)
      exact ⟨RootFrames.row r,s,r,hs,he,fun _ => ⟨hr,rfl⟩,
        fun hh => False.elim (hh hj)⟩
    · refine ⟨A j,1,(0,0),by norm_num,by simp,?_,?_⟩
      · intro hh; exact False.elim (hj hh)
      · intro _
        apply (nonroot_iff_support_card_ne_two (A j) (hsum j) (hne j)).mpr
        intro hc
        exact hj ((mem_rootIndices A j).mpr hc)
  choose B s r hs hrows hroot hnonroot using hchoose
  have hinj : Set.InjOn r (rootIndices A) := by
    intro j hj k hk he
    by_contra hjk
    apply hprop j k hjk (s j/s k) (div_pos (hs j) (hs k))
    calc
      A j = s j • RootFrames.row (r j) := by rw [hrows j,(hroot j hj).2]
      _ = (s j/s k) • (s k • RootFrames.row (r k)) := by
        rw [he,smul_smul,div_mul_cancel _ (ne_of_gt (hs k))]
      _ = (s j/s k) • A k := by rw [← (hroot k hk).2,← hrows k]
  refine ⟨{
    rows := B
    scales := s
    roots := r
    positive := hs
    factorization := hrows
    root_proper := fun j hj => (hroot j hj).1
    root_row := fun j hj => (hroot j hj).2
    nonroot := hnonroot
    root_injective := hinj
    root_frame_card := Finset.card_image_of_injOn hinj
    root_frame_noLoops := ?_
    sum_zero := ?_
    row_nonzero := ?_
    represents := represents_of_positive_row_factorization A B hrep id s hs hrows
    cover := ?_ }⟩
  · intro p hp
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
    exact (hroot j hj).1
  · intro j
    apply (sum_zero_smul_iff (B j) (s j) (ne_of_gt (hs j))).mp
    rw [← hrows j]
    exact hsum j
  · intro j hj
    apply hne j
    rw [hrows j,hj,smul_zero]
  · exact cover_of_normalized_frame A B id s (Equiv.refl _)
      (fun j => ne_of_gt (hs j)) (fun j => hrows j) hcover

/-- A chosen normalized frame, with every property exposed by its structure
fields. The only choice is the positive orientation of each actual root row. -/
noncomputable def normalizeFeatureFrame (A : Fin 4 → Point 4)
    (hsum : ∀ j, ∑ i, A j i = 0) (hne : ∀ j, A j ≠ 0)
    (hprop : ∀ j k, j ≠ k → ∀ c : ℝ, 0 < c → A j ≠ c • A k)
    (hrep : Represents A) (hcover : ∀ i, ∃ j, A j i = 0) :
    NormalizedFeatureFrame A :=
  Classical.choice (normalized_feature_frame_exists A hsum hne hprop hrep hcover)

#print axioms normalized_feature_frame_exists
#print axioms normalizeFeatureFrame
end MaxCaterpillar.Fiber.Count65.FrameTransport
