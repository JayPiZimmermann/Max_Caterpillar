import MaxCaterpillar.Fiber.Basic
import MaxCaterpillar.Frontier.Basic
import Mathlib.Logic.Relation
import Mathlib.Topology.Connected.Basic

/-! # The symmetry quotient of the exact maximum fiber

Only positive hidden-neuron rescalings, permutations in each hidden layer,
and permutations of the input coordinates generate this equivalence relation.
No equality of realized functions or replacement by normal forms is used as
an additional identification. The topology is the quotient topology of the
actual parameter-space fiber, including its degenerate points and biases.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber

open BigOperators

variable {N h₁ h₂ : ℕ}

/-- Rescale every first hidden neuron and compensate in the next affine map.
The symmetry lemmas require all entries of `s` to be strictly positive. -/
noncomputable def scaleFirst (net : Network N h₁ h₂) (s : Fin h₁ → ℝ) :
    Network N h₁ h₂ where
  W₁ j i := s j * net.W₁ j i
  b₁ j := s j * net.b₁ j
  W₂ k j := net.W₂ k j / s j
  b₂ := net.b₂
  w₃ := net.w₃
  b₃ := net.b₃

/-- Rescale every second hidden neuron and compensate in the output map. -/
noncomputable def scaleSecond (net : Network N h₁ h₂) (s : Fin h₂ → ℝ) :
    Network N h₁ h₂ where
  W₁ := net.W₁
  b₁ := net.b₁
  W₂ k j := s k * net.W₂ k j
  b₂ k := s k * net.b₂ k
  w₃ k := net.w₃ k / s k
  b₃ := net.b₃

/-- Relabel both hidden layers, including all incident parameters. -/
def permuteHidden (net : Network N h₁ h₂) (p : Equiv.Perm (Fin h₁))
    (q : Equiv.Perm (Fin h₂)) : Network N h₁ h₂ where
  W₁ j i := net.W₁ (p j) i
  b₁ j := net.b₁ (p j)
  W₂ k j := net.W₂ (q k) (p j)
  b₂ k := net.b₂ (q k)
  w₃ k := net.w₃ (q k)
  b₃ := net.b₃

/-- Relabel input columns. Its realized function precomposes the old function
with the inverse permutation of input coordinates. -/
def permuteInputs (net : Network N h₁ h₂) (p : Equiv.Perm (Fin N)) :
    Network N h₁ h₂ where
  W₁ j i := net.W₁ j (p i)
  b₁ := net.b₁
  W₂ := net.W₂
  b₂ := net.b₂
  w₃ := net.w₃
  b₃ := net.b₃

theorem scaleFirst_eval (net : Network N h₁ h₂) (s : Fin h₁ → ℝ)
    (hs : ∀ j, 0 < s j) (x : Point N) :
    (scaleFirst net s).eval x = net.eval x := by
  have hin (j : Fin h₁) :
      (∑ i, s j * net.W₁ j i * x i) + s j * net.b₁ j =
        s j * ((∑ i, net.W₁ j i * x i) + net.b₁ j) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  unfold Network.eval scaleFirst
  apply congrArg (fun z => z + net.b₃)
  apply Finset.sum_congr rfl
  intro k _
  apply congrArg (fun z => net.w₃ k * relu (z + net.b₂ k))
  apply Finset.sum_congr rfl
  intro j _
  rw [hin j, Frontier.relu_mul_pos (hs j)]
  field_simp [ne_of_gt (hs j)]
  ring

theorem scaleSecond_eval (net : Network N h₁ h₂) (s : Fin h₂ → ℝ)
    (hs : ∀ k, 0 < s k) (x : Point N) :
    (scaleSecond net s).eval x = net.eval x := by
  have hin (k : Fin h₂) :
      (∑ j, s k * net.W₂ k j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) +
        s k * net.b₂ k =
        s k * ((∑ j, net.W₂ k j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) +
          net.b₂ k) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)
  unfold Network.eval scaleSecond
  apply congrArg (fun z => z + net.b₃)
  apply Finset.sum_congr rfl
  intro k _
  rw [hin k, Frontier.relu_mul_pos (hs k)]
  field_simp [ne_of_gt (hs k)]
  ring

theorem permuteHidden_eval (net : Network N h₁ h₂) (p : Equiv.Perm (Fin h₁))
    (q : Equiv.Perm (Fin h₂)) (x : Point N) :
    (permuteHidden net p q).eval x = net.eval x := by
  have hin (k : Fin h₂) :
      (∑ j, net.W₂ (q k) (p j) * relu ((∑ i, net.W₁ (p j) i * x i) + net.b₁ (p j))) =
        ∑ j, net.W₂ (q k) j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j) :=
    Fintype.sum_equiv p _ _ (fun _ => rfl)
  unfold Network.eval permuteHidden
  simp only [hin]
  apply congrArg (fun z => z + net.b₃)
  exact Fintype.sum_equiv q _ _ (fun _ => rfl)

theorem permuteInputs_eval (net : Network N h₁ h₂) (p : Equiv.Perm (Fin N))
    (x : Point N) :
    (permuteInputs net p).eval x = net.eval (fun i => x (p.symm i)) := by
  have hin (j : Fin h₁) :
      (∑ i, net.W₁ j (p i) * x i) = ∑ i, net.W₁ j i * x (p.symm i) := by
    exact Fintype.sum_equiv p _ _ (fun i => by rw [p.symm_apply_apply])
  simp only [Network.eval, permuteInputs, hin]

theorem maximum_permute [NeZero N] (p : Equiv.Perm (Fin N)) (x : Point N) :
    Maximum N (fun i => x (p i)) = Maximum N x := by
  apply le_antisymm
  · exact (Frontier.Maximum_le_iff _ _).2 (fun i => Frontier.le_Maximum x (p i))
  · apply (Frontier.Maximum_le_iff _ _).2
    intro i
    simpa only [p.apply_symm_apply] using
      Frontier.le_Maximum (fun j => x (p j)) (p.symm i)

/-- Bias contraction commutes with positive first-neuron rescaling. The
algebraic identity itself also holds for arbitrary real scale entries. -/
theorem scaleBias_scaleFirst (net : Network N h₁ h₂) (s : Fin h₁ → ℝ) (c : ℝ) :
    (scaleFirst net s).scaleBias c = scaleFirst (net.scaleBias c) s := by
  unfold scaleFirst Network.scaleBias
  congr 1
  funext j
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem scaleBias_scaleSecond (net : Network N h₁ h₂) (s : Fin h₂ → ℝ) (c : ℝ) :
    (scaleSecond net s).scaleBias c = scaleSecond (net.scaleBias c) s := by
  unfold scaleSecond Network.scaleBias
  congr 1
  funext k
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem scaleBias_permuteHidden (net : Network N h₁ h₂)
    (p : Equiv.Perm (Fin h₁)) (q : Equiv.Perm (Fin h₂)) (c : ℝ) :
    (permuteHidden net p q).scaleBias c = permuteHidden (net.scaleBias c) p q := rfl

theorem scaleBias_permuteInputs (net : Network N h₁ h₂)
    (p : Equiv.Perm (Fin N)) (c : ℝ) :
    (permuteInputs net p).scaleBias c = permuteInputs (net.scaleBias c) p := rfl

theorem continuous_scaleFirst (s : Fin h₁ → ℝ) :
    Continuous (fun net : Network N h₁ h₂ => scaleFirst net s) := by
  apply (continuous_network_iff _).2
  refine ⟨?_, ?_, ?_, continuous_b₂, continuous_w₃, continuous_b₃⟩
  · apply continuous_pi
    intro j
    apply continuous_pi
    intro i
    exact continuous_const.mul
      ((continuous_apply i).comp ((continuous_apply j).comp continuous_W₁))
  · apply continuous_pi
    intro j
    exact continuous_const.mul ((continuous_apply j).comp continuous_b₁)
  · apply continuous_pi
    intro k
    apply continuous_pi
    intro j
    exact ((continuous_apply j).comp ((continuous_apply k).comp continuous_W₂)).div_const (s j)

theorem continuous_scaleSecond (s : Fin h₂ → ℝ) :
    Continuous (fun net : Network N h₁ h₂ => scaleSecond net s) := by
  apply (continuous_network_iff _).2
  refine ⟨continuous_W₁, continuous_b₁, ?_, ?_, ?_, continuous_b₃⟩
  · apply continuous_pi
    intro k
    apply continuous_pi
    intro j
    exact continuous_const.mul
      ((continuous_apply j).comp ((continuous_apply k).comp continuous_W₂))
  · apply continuous_pi
    intro k
    exact continuous_const.mul ((continuous_apply k).comp continuous_b₂)
  · apply continuous_pi
    intro k
    exact ((continuous_apply k).comp continuous_w₃).div_const (s k)

theorem continuous_permuteHidden (p : Equiv.Perm (Fin h₁)) (q : Equiv.Perm (Fin h₂)) :
    Continuous (fun net : Network N h₁ h₂ => permuteHidden net p q) := by
  apply (continuous_network_iff _).2
  refine ⟨?_, ?_, ?_, ?_, ?_, continuous_b₃⟩
  · apply continuous_pi
    intro j
    exact (continuous_apply (p j)).comp continuous_W₁
  · apply continuous_pi
    intro j
    exact (continuous_apply (p j)).comp continuous_b₁
  · apply continuous_pi
    intro k
    apply continuous_pi
    intro j
    exact (continuous_apply (p j)).comp ((continuous_apply (q k)).comp continuous_W₂)
  · apply continuous_pi
    intro k
    exact (continuous_apply (q k)).comp continuous_b₂
  · apply continuous_pi
    intro k
    exact (continuous_apply (q k)).comp continuous_w₃

theorem continuous_permuteInputs (p : Equiv.Perm (Fin N)) :
    Continuous (fun net : Network N h₁ h₂ => permuteInputs net p) := by
  apply (continuous_network_iff _).2
  refine ⟨?_, continuous_b₁, continuous_W₂, continuous_b₂, continuous_w₃, continuous_b₃⟩
  apply continuous_pi
  intro j
  apply continuous_pi
  intro i
  exact (continuous_apply (p i)).comp ((continuous_apply j).comp continuous_W₁)

variable [NeZero N]

/-- Positive first-hidden-neuron rescaling restricted to the exact fiber. -/
noncomputable def scaleFirstFiber (s : Fin h₁ → ℝ) (hs : ∀ j, 0 < s j)
    (net : ExactFiber N h₁ h₂) : ExactFiber N h₁ h₂ :=
  ⟨scaleFirst net.val s, fun x => (scaleFirst_eval net.val s hs x).trans (net.property x)⟩

/-- Positive second-hidden-neuron rescaling restricted to the exact fiber. -/
noncomputable def scaleSecondFiber (s : Fin h₂ → ℝ) (hs : ∀ k, 0 < s k)
    (net : ExactFiber N h₁ h₂) : ExactFiber N h₁ h₂ :=
  ⟨scaleSecond net.val s, fun x => (scaleSecond_eval net.val s hs x).trans (net.property x)⟩

def permuteHiddenFiber (p : Equiv.Perm (Fin h₁)) (q : Equiv.Perm (Fin h₂))
    (net : ExactFiber N h₁ h₂) : ExactFiber N h₁ h₂ :=
  ⟨permuteHidden net.val p q, fun x => (permuteHidden_eval net.val p q x).trans (net.property x)⟩

def permuteInputsFiber (p : Equiv.Perm (Fin N))
    (net : ExactFiber N h₁ h₂) : ExactFiber N h₁ h₂ :=
  ⟨permuteInputs net.val p, fun x => by
    rw [permuteInputs_eval, net.property, maximum_permute]⟩

theorem continuous_scaleFirstFiber (s : Fin h₁ → ℝ) (hs : ∀ j, 0 < s j) :
    Continuous (@scaleFirstFiber N h₁ h₂ _ s hs) :=
  ((continuous_scaleFirst s).comp continuous_subtype_val).subtype_mk _

theorem continuous_scaleSecondFiber (s : Fin h₂ → ℝ) (hs : ∀ k, 0 < s k) :
    Continuous (@scaleSecondFiber N h₁ h₂ _ s hs) :=
  ((continuous_scaleSecond s).comp continuous_subtype_val).subtype_mk _

theorem continuous_permuteHiddenFiber (p : Equiv.Perm (Fin h₁))
    (q : Equiv.Perm (Fin h₂)) :
    Continuous (@permuteHiddenFiber N h₁ h₂ _ p q) :=
  ((continuous_permuteHidden p q).comp continuous_subtype_val).subtype_mk _

theorem continuous_permuteInputsFiber (p : Equiv.Perm (Fin N)) :
    Continuous (@permuteInputsFiber N h₁ h₂ _ p) :=
  ((continuous_permuteInputs p).comp continuous_subtype_val).subtype_mk _

/-- Exactly the allowed generating operations. In particular, there is no
generator asserting that arbitrary equal-function networks are equivalent. -/
inductive SymmetryStep : ExactFiber N h₁ h₂ → ExactFiber N h₁ h₂ → Prop
  | first (net : ExactFiber N h₁ h₂) (s : Fin h₁ → ℝ) (hs : ∀ j, 0 < s j) :
      SymmetryStep net (scaleFirstFiber s hs net)
  | second (net : ExactFiber N h₁ h₂) (s : Fin h₂ → ℝ) (hs : ∀ k, 0 < s k) :
      SymmetryStep net (scaleSecondFiber s hs net)
  | hidden (net : ExactFiber N h₁ h₂)
      (p : Equiv.Perm (Fin h₁)) (q : Equiv.Perm (Fin h₂)) :
      SymmetryStep net (permuteHiddenFiber p q net)
  | input (net : ExactFiber N h₁ h₂) (p : Equiv.Perm (Fin N)) :
      SymmetryStep net (permuteInputsFiber p net)

/-- Equivalence under finite compositions of the stated genuine symmetries. -/
def symmetrySetoid (N h₁ h₂ : ℕ) [NeZero N] : Setoid (ExactFiber N h₁ h₂) where
  r := EqvGen SymmetryStep
  iseqv := EqvGen.is_equivalence SymmetryStep

/-- The actual exact fiber modulo the stated symmetries, with quotient topology. -/
abbrev SymmetryQuotient (N h₁ h₂ : ℕ) [NeZero N] := Quotient (symmetrySetoid N h₁ h₂)

def quotientMk : ExactFiber N h₁ h₂ → SymmetryQuotient N h₁ h₂ :=
  Quotient.mk (symmetrySetoid N h₁ h₂)

theorem quotientMk_surjective : Function.Surjective (@quotientMk N h₁ h₂ _) :=
  Quot.exists_rep

theorem quotientMk_continuous : Continuous (@quotientMk N h₁ h₂ _) :=
  @continuous_quotient_mk' (ExactFiber N h₁ h₂) _ (symmetrySetoid N h₁ h₂)

theorem quotientMk_quotientMap : QuotientMap (@quotientMk N h₁ h₂ _) :=
  @quotientMap_quotient_mk' (ExactFiber N h₁ h₂) _ (symmetrySetoid N h₁ h₂)

theorem quotientMk_eq_iff (net net' : ExactFiber N h₁ h₂) :
    quotientMk net = quotientMk net' ↔ EqvGen SymmetryStep net net' :=
  ⟨@Quotient.exact _ (symmetrySetoid N h₁ h₂) net net',
    @Quotient.sound _ (symmetrySetoid N h₁ h₂) net net'⟩

theorem quotientMk_eq_of_step {net net' : ExactFiber N h₁ h₂}
    (h : SymmetryStep net net') : quotientMk net = quotientMk net' :=
  @Quotient.sound _ (symmetrySetoid N h₁ h₂) net net' (EqvGen.rel _ _ h)

/-- An exact component-count proposition; its topology is that of the genuine
symmetry quotient, not the topology of a proposed normal-form parameterization. -/
def HasComponentCount (N h₁ h₂ count : ℕ) [NeZero N] : Prop :=
  Nonempty (ConnectedComponents (SymmetryQuotient N h₁ h₂) ≃ Fin count)

end MaxCaterpillar.Fiber
