import MaxCaterpillar.Frontier.Basic

/-!
An explicit shallow function invisible on every MAX5 triple-contact cone.
It is not a network computing MAX5 and does not settle any width endpoint.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Frontier.Max5Invisible

open BigOperators Filter Topology

def u (x : Point 5) : ℝ := x 0 + x 3 + x 4 - 2 * x 1 - 2 * x 2

noncomputable def invisible (x : Point 5) : ℝ :=
  relu (u x + x 0) + relu (u x + x 3) + relu (u x + x 4) -
    2 * relu (u x + x 1) - 2 * relu (u x + x 2)

def contact (i j : Fin 5) (s t : ℝ) : Point 5 :=
  fun k => -(if k = i then s else 0) - (if k = j then t else 0)

def coefficient (i : Fin 5) : ℝ := if i.val = 1 ∨ i.val = 2 then -2 else 1

def firstRow (i : Fin 5) : Point 5 :=
  fun k => coefficient k + if k = i then 1 else 0

lemma coefficient_cases (i : Fin 5) : coefficient i = 1 ∨ coefficient i = -2 := by
  unfold coefficient
  split_ifs <;> simp

@[simp] lemma coefficient_zero : coefficient 0 = 1 := rfl
@[simp] lemma coefficient_one : coefficient 1 = -2 := rfl
@[simp] lemma coefficient_two : coefficient 2 = -2 := rfl
@[simp] lemma coefficient_three : coefficient 3 = 1 := rfl
@[simp] lemma coefficient_four : coefficient 4 = 1 := rfl

lemma coefficient_sum : ∑ i, coefficient i = -1 := by
  norm_num [Fin.sum_univ_five]

lemma u_eq_lin (x : Point 5) : u x = lin coefficient x := by
  simp [lin, Fin.sum_univ_five, u]
  ring

lemma firstRow_eval (i : Fin 5) (x : Point 5) : lin (firstRow i) x = u x + x i := by
  rw [u_eq_lin]
  simp [lin, firstRow, add_mul, Finset.sum_add_distrib, ite_mul]

/-- A literal five-neuron shallow representation, with no affine biases. -/
theorem shallow_representation (x : Point 5) :
    invisible x = ∑ i, coefficient i * relu (lin (firstRow i) x) := by
  simp only [firstRow_eval]
  simp [Fin.sum_univ_five, invisible]
  ring

lemma weighted_relu (x : Point 5) :
    invisible x = ∑ i, coefficient i * relu (u x + x i) := by
  simpa only [firstRow_eval] using shallow_representation x

/-- All five first normals annihilate common translation. -/
theorem firstRow_sum (i : Fin 5) : ∑ k, firstRow i k = 0 := by
  simp [firstRow, Finset.sum_add_distrib, coefficient_sum]

/-- Every one of the five first normals has all five coordinates nonzero. -/
theorem firstRow_full_support (i k : Fin 5) : firstRow i k ≠ 0 := by
  unfold firstRow
  by_cases hk : k = i
  · rw [if_pos hk]
    rcases coefficient_cases k with h | h <;> rw [h] <;> norm_num
  · rw [if_neg hk]
    rcases coefficient_cases k with h | h <;> rw [h] <;> norm_num

lemma linear_cancellation (x : Point 5) : ∑ i, coefficient i * (u x + x i) = 0 := by
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, coefficient_sum]
  rw [show (∑ i, coefficient i * x i) = u x from (u_eq_lin x).symm]
  ring

lemma invisible_of_nonpos (x : Point 5) (h : ∀ i, u x + x i ≤ 0) : invisible x = 0 := by
  rw [weighted_relu]
  simp only [relu_of_nonpos (h _), mul_zero, Finset.sum_const_zero]

lemma invisible_of_nonneg (x : Point 5) (h : ∀ i, 0 ≤ u x + x i) : invisible x = 0 := by
  rw [weighted_relu]
  simpa only [relu_of_nonneg (h _)] using linear_cancellation x

lemma u_contact (i j : Fin 5) (s t : ℝ) :
    u (contact i j s t) = -s * coefficient i - t * coefficient j := by
  rw [u_eq_lin]
  simp [lin, contact, mul_sub, mul_neg, mul_ite, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  ring

lemma contact_comm (i j : Fin 5) (s t : ℝ) : contact i j s t = contact j i t s := by
  funext k
  unfold contact
  ring

lemma contact_formula (i j : Fin 5) (hij : i ≠ j) (s t : ℝ) :
    invisible (contact i j s t) =
      (-1 - coefficient i - coefficient j) * relu (u (contact i j s t)) +
      coefficient i * relu (u (contact i j s t) - s) +
      coefficient j * relu (u (contact i j s t) - t) := by
  rw [weighted_relu]
  let z := u (contact i j s t)
  have hterm : ∀ k, coefficient k * relu (u (contact i j s t) + contact i j s t k) =
      coefficient k * relu z +
        (if k = i then coefficient i * (relu (z - s) - relu z) else 0) +
        (if k = j then coefficient j * (relu (z - t) - relu z) else 0) := by
    intro k
    by_cases hki : k = i
    · subst k
      simp [contact, hij, z]
      ring
    · by_cases hkj : k = j
      · subst k
        simp [contact, hij.symm, z]
        ring
      · simp [contact, hki, hkj, z]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, coefficient_sum]
  simp
  ring

lemma mixed_contact_zero (i j : Fin 5) (hi : coefficient i = 1)
    (hj : coefficient j = -2) (s t : ℝ) : invisible (contact i j s t) = 0 := by
  have hij : i ≠ j := by intro he; rw [he, hj] at hi; norm_num at hi
  rw [contact_formula i j hij, u_contact, hi, hj]
  have htwo := relu_mul_pos (by norm_num : (0 : ℝ) < 2) (t - s)
  have e1 : -s * 1 - t * (-2) - s = 2 * (t - s) := by ring
  have e2 : -s * 1 - t * (-2) - t = t - s := by ring
  rw [e1, e2, htwo]
  ring

theorem translation_invariant (x : Point 5) (t : ℝ) :
    invisible (fun i => x i + t) = invisible x := by
  unfold invisible u
  congr 2 <;> ring

theorem even (x : Point 5) : invisible (-x) = invisible x := by
  have hu : u (-x) = -u x := by simp only [u, Pi.neg_apply]; ring
  have h0 := relu_sub_relu_neg (u x + x 0)
  have h1 := relu_sub_relu_neg (u x + x 1)
  have h2 := relu_sub_relu_neg (u x + x 2)
  have h3 := relu_sub_relu_neg (u x + x 3)
  have h4 := relu_sub_relu_neg (u x + x 4)
  simp only [invisible, hu, Pi.neg_apply, ← neg_add]
  unfold u at *
  linarith only [h0, h1, h2, h3, h4]

theorem contact_zero (i j : Fin 5) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    invisible (contact i j s t) = 0 := by
  rcases coefficient_cases i with hi | hi <;> rcases coefficient_cases j with hj | hj
  · apply invisible_of_nonpos
    intro k
    rw [u_contact, hi, hj]
    unfold contact
    split_ifs <;> linarith
  · exact mixed_contact_zero i j hi hj s t
  · rw [contact_comm]
    exact mixed_contact_zero j i hj hi t s
  · apply invisible_of_nonneg
    intro k
    rw [u_contact, hi, hj]
    unfold contact
    split_ifs <;> linarith

theorem nonzero_witness : invisible ![0, 0, 2, 1, 2] = -1 := by
  have h3 : (![0, 0, 2, 1, 2] : Point 5) 3 = 1 := rfl
  have h4 : (![0, 0, 2, 1, 2] : Point 5) 4 = 2 := rfl
  norm_num [invisible, u, relu, h3, h4]

/-- Includes every common translation of every two-coordinate negative
cone. These are precisely the MAX5 inputs with at least three top ties. -/
theorem shifted_contact_zero (i j : Fin 5) (m s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    invisible (fun k => m - (if k = i then s else 0) - (if k = j then t else 0)) = 0 := by
  have heq : (fun k => m - (if k = i then s else 0) - (if k = j then t else 0)) =
      (fun k => contact i j s t k + m) := by
    funext k
    unfold contact
    ring
  rw [heq, translation_invariant, contact_zero i j s t hs ht]

lemma continuous_preactivation (k : Fin 5) : Continuous (fun x : Point 5 => u x + x k) := by
  unfold u
  continuity

lemma preactivation_at_vertex (i k : Fin 5) :
    u (-unitVec i) + (-unitVec i) k = -coefficient i - (if k = i then 1 else 0) := by
  have heq : (-unitVec i : Point 5) = contact i i 1 0 := by
    funext k
    simp [unitVec, contact, Pi.neg_apply]
  rw [heq, u_contact]
  simp [contact]
  ring

/-- The function vanishes on an open neighborhood of every four-way
contact, so all local germs there are unchanged by adding this function. -/
theorem eventually_zero_at_vertex (i : Fin 5) :
    ∀ᶠ x in 𝓝 (-unitVec i : Point 5), invisible x = 0 := by
  rcases coefficient_cases i with hi | hi
  · have hstrict : ∀ k, u (-unitVec i) + (-unitVec i) k < 0 := by
      intro k
      rw [preactivation_at_vertex, hi]
      split_ifs <;> norm_num
    have hev : ∀ᶠ x in 𝓝 (-unitVec i : Point 5), ∀ k, u x + x k < 0 :=
      Filter.eventually_all.mpr fun k =>
        (continuous_preactivation k).continuousAt.eventually (eventually_lt_nhds (hstrict k))
    exact hev.mono fun x hx => invisible_of_nonpos x (fun k => (hx k).le)
  · have hstrict : ∀ k, 0 < u (-unitVec i) + (-unitVec i) k := by
      intro k
      rw [preactivation_at_vertex, hi]
      split_ifs <;> norm_num
    have hev : ∀ᶠ x in 𝓝 (-unitVec i : Point 5), ∀ k, 0 < u x + x k :=
      Filter.eventually_all.mpr fun k =>
        (continuous_preactivation k).continuousAt.eventually (eventually_gt_nhds (hstrict k))
    exact hev.mono fun x hx => invisible_of_nonneg x (fun k => (hx k).le)

/-- Adding the invisible function preserves the odd part of any function. -/
theorem perturbation_odd_part (g : Point 5 → ℝ) (a : ℝ) (x : Point 5) :
    (g x + a * invisible x) - (g (-x) + a * invisible (-x)) = g x - g (-x) := by
  rw [even]
  ring

/-- The perturbed function agrees on an actual neighborhood, not only in
its values or first derivatives at the five four-way contacts. -/
theorem perturbation_same_local_germ (g : Point 5 → ℝ) (a : ℝ) (i : Fin 5) :
    ∀ᶠ x in 𝓝 (-unitVec i : Point 5), g x + a * invisible x = g x := by
  exact (eventually_zero_at_vertex i).mono fun x hx => by rw [hx]; ring

#check @translation_invariant
#check @even
#check @contact_zero
#check @nonzero_witness
#print axioms translation_invariant
#print axioms even
#print axioms contact_zero
#print axioms nonzero_witness
#check @shallow_representation
#check @firstRow_sum
#check @firstRow_full_support
#check @eventually_zero_at_vertex
#print axioms shallow_representation
#print axioms firstRow_sum
#print axioms firstRow_full_support
#print axioms eventually_zero_at_vertex
#check @shifted_contact_zero
#check @perturbation_odd_part
#check @perturbation_same_local_germ
#print axioms shifted_contact_zero
#print axioms perturbation_odd_part
#print axioms perturbation_same_local_germ

end MaxCaterpillar.Frontier.Max5Invisible
