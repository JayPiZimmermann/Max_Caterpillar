import MaxNN.Constructions.Paramid.Caterpillar.Geometry.BaseGerm
import MaxNN.Constructions.Paramid.Caterpillar.Words.Join

/-! # Endpoint cancellation for actual concatenated caterpillar words

The pointwise word-joining identity connects `caterpillarUnit` to `joinedUnit`.
Thus the endpoint-fibre cancellation applies to the original units, with the
boundary included as a spine cut. Reindexing the complete permutation sum into
these fibres and proving the global coefficient identity remain separate tasks.
-/

open BigOperators

namespace MaxNN.Caterpillar

open ParamidGeom

variable {m r s : ℕ}

theorem values_append (A : Fin (r + 1) → Fin m → ℝ)
    (B : Fin (s + 1) → Fin m → ℝ) (y : Fin m → ℝ) :
    values (r := r + 1 + s) (Fin.append (m := r + 1) (n := s + 1) A B) y =
      Fin.append (m := r + 1) (n := s + 1) (values A y) (values B y) := by
  funext i
  refine Fin.addCases (m := r + 1) (n := s + 1)
    (motive := fun j : Fin ((r + 1) + (s + 1)) =>
      dot (Fin.append A B j) y = Fin.append (values A y) (values B y) j)
    (fun j => ?_) (fun j => ?_) i
  · simp only [values, Fin.append_left]
  · simp only [values, Fin.append_right]

theorem caterpillarUnit_join (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (B : Fin (s + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (T : Finset (Fin (s + 1))) :
    caterpillarUnit (r := r + 1 + s) apex
      (Fin.append (m := r + 1) (n := s + 1) A B) (joinCuts S T) =
      joinedUnit apex A B S T := by
  funext y
  unfold caterpillarUnit joinedUnit
  rw [values_append A B y, baseMax_join (values A y) (values B y) S T]
  rfl

/-- The actual concatenated caterpillar units cancel over the left cut set,
modulo `LSpan m 1`, in the normalized non-apex block direction. -/
theorem sum_germDiff_caterpillarUnit_join_mem_LSpan_one (hr : 1 ≤ r) (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (B : Fin (s + 1) → Fin m → ℝ)
    (T : Finset (Fin (s + 1))) (u : Fin m → ℝ) (ha : dot apex u = 0)
    (hA : ∀ i, dot (A i) u = -1) (hB : ∀ i, dot (B i) u = 0) :
    (fun y => ∑ S in (cutPositions r).powerset,
      (-1 : ℝ) ^ S.card * germDiff u
        (caterpillarUnit (r := r + 1 + s) apex
          (Fin.append (m := r + 1) (n := s + 1) A B) (joinCuts S T)) y) ∈
      LSpan m 1 := by
  simp_rw [caterpillarUnit_join]
  exact sum_germDiff_joinedUnit_block_mem_LSpan_one hr apex A B T u ha hA hB

/-- The sign is computed from the full joined cut set. The extra exponent
`q` allows the arity-dependent global sign without changing the argument. -/
theorem sum_germDiff_caterpillarUnit_join_card_mem_LSpan_one (hr : 1 ≤ r)
    (q : ℕ) (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (B : Fin (s + 1) → Fin m → ℝ)
    (T : Finset (Fin (s + 1))) (hT : (0 : Fin (s + 1)) ∉ T)
    (u : Fin m → ℝ) (ha : dot apex u = 0)
    (hA : ∀ i, dot (A i) u = -1) (hB : ∀ i, dot (B i) u = 0) :
    (fun y => ∑ S in (cutPositions r).powerset,
      (-1 : ℝ) ^ (q + (joinCuts S T).card) * germDiff u
        (caterpillarUnit (r := r + 1 + s) apex
          (Fin.append (m := r + 1) (n := s + 1) A B) (joinCuts S T)) y) ∈
      LSpan m 1 := by
  have hp : ∀ S : Finset (Fin (r + 1)),
      (-1 : ℝ) ^ (q + (joinCuts S T).card) =
        (-1 : ℝ) ^ (q + T.card + 1) * (-1 : ℝ) ^ S.card := by
    intro S
    rw [card_joinCuts S T hT,
      show q + (S.card + T.card + 1) = (q + T.card + 1) + S.card by ac_rfl, pow_add]
  have h := Submodule.smul_mem (LSpan m 1) ((-1 : ℝ) ^ (q + T.card + 1))
    (sum_germDiff_caterpillarUnit_join_mem_LSpan_one hr apex A B T u ha hA hB)
  have he : (fun y => ∑ S in (cutPositions r).powerset,
      (-1 : ℝ) ^ (q + (joinCuts S T).card) * germDiff u
        (caterpillarUnit (r := r + 1 + s) apex
          (Fin.append (m := r + 1) (n := s + 1) A B) (joinCuts S T)) y) =
      (-1 : ℝ) ^ (q + T.card + 1) • (fun y => ∑ S in (cutPositions r).powerset,
        (-1 : ℝ) ^ S.card * germDiff u
          (caterpillarUnit (r := r + 1 + s) apex
            (Fin.append (m := r + 1) (n := s + 1) A B) (joinCuts S T)) y) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, hp, mul_assoc]
  rwa [he]

end MaxNN.Caterpillar
