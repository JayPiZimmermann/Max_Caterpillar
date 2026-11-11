import MaxCaterpillar.Frontier.StarCertificate.SignedForms

/-! # Piecewise-linear Xi and its signed-selector linearization

The coefficient dictionary is arbitrary in this file. Its finite values are
checked separately; this bridge proves that sign-only coefficient arithmetic
has the claimed meaning on every real input.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

def Sign.direction : Sign → ℚ
  | .neg => -1
  | .zero => 0
  | .pos => 1

def normalizeSign (orientation s : Sign) : Sign :=
  match orientation with
  | .neg => s.opposite
  | .zero => .zero
  | .pos => s

def headSign (p : Fin 4 → Sign) : Sign :=
  if p 0 ≠ .zero then p 0 else
  if p 1 ≠ .zero then p 1 else
  if p 2 ≠ .zero then p 2 else p 3

def Mixed (p : Fin 4 → Sign) : Prop :=
  (∃ i, p i = .neg) ∧ (∃ i, p i = .pos)

instance mixedDecidable (p : Fin 4 → Sign) : Decidable (Mixed p) := by
  unfold Mixed
  infer_instance

noncomputable def coordinateSigns (gamma : Fin 4 → ℝ) : Fin 4 → Sign :=
  fun i => signOf (gamma i)

/-- The certificate's actual function on chain vectors. The coarse forms H
are evaluated on the chain itself; no face representative occurs here. -/
noncomputable def xi {h : ℕ} (H : Fin h → RationalForm 4)
    (omega : RationalForm 4) (kappa : (Fin h → Sign) → RationalForm 4)
    (gamma : Fin 4 → ℝ) : ℝ :=
  let orientation := headSign (coordinateSigns gamma)
  let normalized := fun t => normalizeSign orientation (actualSigns H gamma t)
  let weights := if Mixed (coordinateSigns gamma) then kappa normalized else omega
  (orientation.direction : ℝ) * evalForm weights gamma

/-- Symbolic coefficients obtained solely from the signs of the tested
forms. All chain and coarse-form occurrences are signed references. -/
def xiCoefficients {m n h : ℕ} (A : Fin m → RationalForm n)
    (omega : RationalForm 4) (kappa : (Fin h → Sign) → RationalForm 4)
    (chain : Fin 4 → FormRef m) (coarse : Fin h → FormRef m)
    (p : Fin m → Sign) : RationalForm n :=
  let chainSigns := fun j => (chain j).sign p
  let orientation := headSign chainSigns
  let normalized := fun t => normalizeSign orientation ((coarse t).sign p)
  let weights := if Mixed chainSigns then kappa normalized else omega
  fun i => ∑ j, (orientation.direction * weights j) * (chain j).form A i

theorem eval_coarse_reference {m n h : ℕ} (A : Fin m → RationalForm n)
    (H : Fin h → RationalForm 4) (chain : Fin 4 → FormRef m)
    (coarse : Fin h → FormRef m)
    (compatible : ∀ t i, (coarse t).form A i = ∑ j, H t j * (chain j).form A i)
    (x : Fin n → ℝ) (t : Fin h) :
    evalForm (H t) (fun j => evalForm ((chain j).form A) x) =
      evalForm ((coarse t).form A) x := by
  have he : (coarse t).form A = fun i => ∑ j, H t j * (chain j).form A i := by
    funext i
    exact compatible t i
  rw [he, evalForm_combination]
  rfl

/-- The load-bearing semantic bridge: the piecewise Xi expression equals
the rational linear form computed from the actual subset-sum signs. -/
theorem xi_eq_evalForm_coefficients {m n h : ℕ}
    (A : Fin m → RationalForm n) (H : Fin h → RationalForm 4)
    (omega : RationalForm 4) (kappa : (Fin h → Sign) → RationalForm 4)
    (chain : Fin 4 → FormRef m) (coarse : Fin h → FormRef m)
    (compatible : ∀ t i, (coarse t).form A i = ∑ j, H t j * (chain j).form A i)
    (x : Fin n → ℝ) :
    xi H omega kappa (fun j => evalForm ((chain j).form A) x) =
      evalForm (xiCoefficients A omega kappa chain coarse (actualSigns A x)) x := by
  have hc : coordinateSigns (fun j => evalForm ((chain j).form A) x) =
      fun j => (chain j).sign (actualSigns A x) := by
    funext j
    exact (chain j).actual_sign A x
  have hh : actualSigns H (fun j => evalForm ((chain j).form A) x) =
      fun t => (coarse t).sign (actualSigns A x) := by
    funext t
    change signOf (evalForm (H t) (fun j => evalForm ((chain j).form A) x)) = _
    rw [eval_coarse_reference A H chain coarse compatible x t]
    exact (coarse t).actual_sign A x
  unfold xi xiCoefficients
  rw [hc, hh]
  dsimp only
  rw [evalForm_combination]
  simp only [Rat.cast_mul, evalForm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

end MaxCaterpillar.Frontier.StarCertificate

namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem headSign_opposite : ∀ p : Fin 4 → Sign,
    headSign (fun i => (p i).opposite) = (headSign p).opposite := by decide

theorem mixed_opposite : ∀ p : Fin 4 → Sign,
    Mixed (fun i => (p i).opposite) ↔ Mixed p := by decide

@[simp] theorem direction_opposite (s : Sign) : s.opposite.direction = -s.direction := by
  cases s <;> rfl

@[simp] theorem normalize_opposite (a b : Sign) :
    normalizeSign a.opposite b.opposite = normalizeSign a b := by
  cases a <;> cases b <;> rfl

@[simp] theorem coordinateSigns_neg (gamma : Fin 4 → ℝ) :
    coordinateSigns (fun i => -gamma i) = fun i => (coordinateSigns gamma i).opposite := by
  funext i
  exact signOf_neg (gamma i)

@[simp] theorem evalForm_neg_input {n : ℕ} (a : RationalForm n) (x : Fin n → ℝ) :
    evalForm a (fun i => -x i) = -evalForm a x := by
  simp only [evalForm, mul_neg, Finset.sum_neg_distrib]

@[simp] theorem actualSigns_neg {m n : ℕ} (A : Fin m → RationalForm n) (x : Fin n → ℝ) :
    actualSigns A (fun i => -x i) = fun j => (actualSigns A x j).opposite := by
  funext j
  simp only [actualSigns, evalForm_neg_input, signOf_neg]

/-- Evenness holds for every dictionary, including all equality strata. -/
theorem xi_neg {h : ℕ} (H : Fin h → RationalForm 4)
    (omega : RationalForm 4) (kappa : (Fin h → Sign) → RationalForm 4)
    (gamma : Fin 4 → ℝ) : xi H omega kappa (fun i => -gamma i) = xi H omega kappa gamma := by
  unfold xi
  simp only [coordinateSigns_neg, actualSigns_neg, headSign_opposite, normalize_opposite,
    mixed_opposite, direction_opposite, Rat.cast_neg, evalForm_neg_input, neg_mul_neg]

theorem signOf_mul_pos (c a : ℝ) (hc : 0 < c) : signOf (c*a) = signOf a := by
  apply Eq.symm
  apply Sign.eq_signOf
  have ha := signOf_holds a
  cases hs : signOf a <;> rw [hs] at ha
  · exact mul_neg_of_pos_of_neg hc ha
  · change c*a = 0
    change a = 0 at ha
    rw [ha, mul_zero]
  · exact mul_pos hc ha

@[simp] theorem evalForm_mul_input {n : ℕ} (a : RationalForm n)
    (x : Fin n → ℝ) (c : ℝ) :
    evalForm a (fun i => c*x i) = c*evalForm a x := by
  simp only [evalForm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Positive homogeneity holds for every dictionary. -/
theorem xi_mul_pos {h : ℕ} (H : Fin h → RationalForm 4)
    (omega : RationalForm 4) (kappa : (Fin h → Sign) → RationalForm 4)
    (gamma : Fin 4 → ℝ) (c : ℝ) (hc : 0 < c) :
    xi H omega kappa (fun i => c*gamma i) = c*xi H omega kappa gamma := by
  have hs : coordinateSigns (fun i => c*gamma i) = coordinateSigns gamma := by
    funext i
    exact signOf_mul_pos c (gamma i) hc
  have hh : actualSigns H (fun i => c*gamma i) = actualSigns H gamma := by
    funext j
    simp only [actualSigns, evalForm_mul_input]
    exact signOf_mul_pos c (evalForm (H j) gamma) hc
  unfold xi
  rw [hs, hh]
  dsimp only
  rw [evalForm_mul_input]
  ring

theorem xi_zero {h : ℕ} (H : Fin h → RationalForm 4)
    (omega : RationalForm 4) (kappa : (Fin h → Sign) → RationalForm 4) :
    xi H omega kappa 0 = 0 := by
  unfold xi evalForm
  simp

/-- Agreement with the prescribed linear weight on nonmixed vectors. The
orientation is the sign of the first nonzero chain coordinate. -/
theorem xi_nonmixed {h : ℕ} (H : Fin h → RationalForm 4)
    (omega : RationalForm 4) (kappa : (Fin h → Sign) → RationalForm 4)
    (gamma : Fin 4 → ℝ) (hm : ¬ Mixed (coordinateSigns gamma)) :
    xi H omega kappa gamma =
      ((headSign (coordinateSigns gamma)).direction : ℝ) * evalForm omega gamma := by
  simp only [xi, if_neg hm]

end MaxCaterpillar.Frontier.StarCertificate
