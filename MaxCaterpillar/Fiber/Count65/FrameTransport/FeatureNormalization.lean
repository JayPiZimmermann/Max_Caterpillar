import MaxCaterpillar.Fiber.Count65.RootNormalization
import MaxCaterpillar.Fiber.Count65.TwoRoots.NetworkBridge

/-! # Transport of arbitrary four-feature maximum representations

All row magnitudes remain real. Positive scales are required only for ReLU
feature transport; nonroot and zero-sum transport use any nonzero scale.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.FrameTransport
open MaxCaterpillar.Frontier BigOperators TwoRoots

theorem nonroot_smul_iff (a : Point 4) (s : ℝ) (hs : s ≠ 0) :
    Nonroot (s • a) ↔ Nonroot a := by
  constructor
  · intro h i k hik hf
    obtain ⟨c,hc⟩ := hf
    apply h i k hik
    refine ⟨s*c,fun l => ?_⟩
    change s*a l = _
    rw [hc l]
    ring
  · intro h i k hik hf
    obtain ⟨c,hc⟩ := hf
    apply h i k hik
    refine ⟨s⁻¹*c,fun l => ?_⟩
    have hh := congrArg (fun z : ℝ => s⁻¹*z) (hc l)
    change s⁻¹*(s*a l) = _ at hh
    simpa only [← mul_assoc,inv_mul_cancel hs,one_mul] using hh

theorem nonroot_permute (a : Point 4) (q : Equiv.Perm (Fin 4))
    (h : Nonroot a) : Nonroot (fun i => a (q i)) := by
  intro i k hik hf
  obtain ⟨c,hc⟩ := hf
  apply h (q i) (q k) (fun he => hik (q.injective he))
  refine ⟨c,fun l => ?_⟩
  have hi : q.symm l = i ↔ l = q i := by
    constructor
    · intro hh; rw [← hh,q.apply_symm_apply]
    · intro hh; rw [hh,q.symm_apply_apply]
  have hk : q.symm l = k ↔ l = q k := by
    constructor
    · intro hh; rw [← hh,q.apply_symm_apply]
    · intro hh; rw [hh,q.symm_apply_apply]
  simpa only [q.apply_symm_apply,hi,hk] using hc (q.symm l)

theorem nonroot_permute_iff (a : Point 4) (q : Equiv.Perm (Fin 4)) :
    Nonroot (fun i => a (q i)) ↔ Nonroot a := by
  constructor
  · intro h
    simpa only [q.apply_symm_apply] using
      nonroot_permute (fun i => a (q i)) q.symm h
  · exact nonroot_permute a q

theorem sum_permute (a : Point 4) (q : Equiv.Perm (Fin 4)) :
    (∑ i, a (q i)) = ∑ i, a i :=
  Fintype.sum_equiv q _ _ (fun i => rfl)

theorem sum_zero_smul_iff (a : Point 4) (s : ℝ) (hs : s ≠ 0) :
    (∑ i, (s • a) i) = 0 ↔ (∑ i, a i) = 0 := by
  simp only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum]
  exact mul_eq_zero.trans (by simp only [hs,false_or])

/-- Nonzero zero-sum covectors are nonroots exactly when their support is
not two. The forward direction uses the positive real root normalization. -/
theorem nonroot_iff_support_card_ne_two (a : Point 4)
    (hsum : ∑ i, a i = 0) (hne : a ≠ 0) :
    Nonroot a ↔ (nonzeroCoordinates a).card ≠ 2 := by
  classical
  constructor
  · intro h hc
    obtain ⟨p,hp,c,_hcpos,he⟩ := positive_root_of_support_two a hsum hc
    apply h p.1 p.2 hp
    refine ⟨c,fun l => ?_⟩
    simpa only [Pi.smul_apply,smul_eq_mul,RootFrames.row] using congrFun he l
  · intro hc
    intro i k hik hf
    obtain ⟨c,hcform⟩ := hf
    have hc0 : c ≠ 0 := by
      intro hz
      apply hne
      funext l
      simp only [Pi.zero_apply]
      rw [hcform l,hz,zero_mul]
    have hsupp : nonzeroCoordinates a = {i,k} := by
      apply Finset.ext
      intro l
      rw [mem_nonzeroCoordinates,hcform l]
      by_cases hli : l = i
      · subst l; simp [hik,hc0]
      by_cases hlk : l = k
      · subst l; simp [Ne.symm hik,hc0]
      · simp [hli,hlk]
    apply hc
    rw [hsupp]
    simp [hik]

/-- An actual row factorization transfers its representation to the
normalized feature dictionary. The observation map may repeat or omit rows;
the decoder lifts the normalized features explicitly. -/
theorem represents_of_positive_row_factorization
    (A B : Fin 4 → Point 4) (hA : Represents A)
    (p : Fin 4 → Fin 4) (s : Fin 4 → ℝ)
    (hs : ∀ j, 0 < s j) (hrows : ∀ j, A j = s j • B (p j)) :
    Represents B := by
  obtain ⟨ell,Phi,h⟩ := hA
  refine ⟨ell,fun z => Phi (fun j => s j*z (p j)),fun x => ?_⟩
  have he : (fun j => relu (lin (A j) x)) =
      (fun j => s j*relu (lin (B (p j)) x)) := by
    funext j
    rw [hrows j,lin_smul_left,relu_mul_pos (hs j)]
  change Maximum 4 x = lin ell x + Phi (fun j => s j*relu (lin (B (p j)) x))
  rw [← he]
  exact h x

/-- The same feature normalization with an arbitrary input relabeling.
The all-input maximum equation discharges the relabeling exactly. -/
theorem represents_of_normalized_frame
    (A B : Fin 4 → Point 4) (hA : Represents A)
    (p : Fin 4 → Fin 4) (s : Fin 4 → ℝ) (q : Equiv.Perm (Fin 4))
    (hs : ∀ j, 0 < s j)
    (hrows : ∀ j, A j = s j • (fun i => B (p j) (q i))) :
    Represents B :=
  Represents.unpermute q
    (represents_of_positive_row_factorization A (fun j i => B j (q i))
      hA p s hs hrows)

/-- Reindexing observations preserves and reflects representability. -/
theorem represents_reindex_iff (A : Fin 4 → Point 4)
    (p : Equiv.Perm (Fin 4)) :
    Represents (fun j => A (p j)) ↔ Represents A := by
  constructor
  · intro h
    exact represents_of_positive_row_factorization _ A h p (fun _ => 1)
      (fun _ => by norm_num) (fun _ => by simp)
  · intro h
    exact represents_of_positive_row_factorization A (fun j => A (p j)) h
      p.symm (fun _ => 1) (fun _ => by norm_num)
      (fun j => by simp only [p.apply_symm_apply,one_smul])

/-- Coordinate-zero coverage is transported from the original rows,
without any surjectivity assumption on the observation map. -/
theorem cover_of_normalized_frame
    (A B : Fin 4 → Point 4) (p : Fin 4 → Fin 4) (s : Fin 4 → ℝ)
    (q : Equiv.Perm (Fin 4)) (hs : ∀ j, s j ≠ 0)
    (hrows : ∀ j, A j = s j • (fun i => B (p j) (q i)))
    (hcover : ∀ i, ∃ j, A j i = 0) : ∀ i, ∃ j, B j i = 0 := by
  intro i
  obtain ⟨j,hj⟩ := hcover (q.symm i)
  have he := congrFun (hrows j) (q.symm i)
  change A j (q.symm i) = s j*B (p j) (q (q.symm i)) at he
  rw [q.apply_symm_apply,hj] at he
  exact ⟨p j,(mul_eq_zero.mp he.symm).resolve_left (hs j)⟩

/-- A row equation transports the nonroot predicate with no sign restriction
on its nonzero scale. -/
theorem nonroot_of_normalized_row (a b : Point 4) (s : ℝ)
    (q : Equiv.Perm (Fin 4)) (hs : s ≠ 0)
    (he : a = s • (fun i => b (q i))) : Nonroot a ↔ Nonroot b := by
  rw [he,nonroot_smul_iff _ s hs,nonroot_permute_iff]

theorem sum_zero_of_normalized_row (a b : Point 4) (s : ℝ)
    (q : Equiv.Perm (Fin 4)) (hs : s ≠ 0)
    (he : a = s • (fun i => b (q i))) :
    (∑ i, a i) = 0 ↔ (∑ i, b i) = 0 := by
  rw [he,sum_zero_smul_iff _ s hs,sum_permute]

#print axioms nonroot_smul_iff
#print axioms nonroot_permute_iff
#print axioms nonroot_iff_support_card_ne_two
#print axioms represents_of_normalized_frame
#print axioms represents_reindex_iff
#print axioms cover_of_normalized_frame
#print axioms nonroot_of_normalized_row
#print axioms sum_zero_of_normalized_row
end MaxCaterpillar.Fiber.Count65.FrameTransport
