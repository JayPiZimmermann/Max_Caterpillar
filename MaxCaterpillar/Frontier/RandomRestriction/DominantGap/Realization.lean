import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.Powers
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.GapPolynomial

/-! # A common generic dominant-gap scale for actual raw permutations

All tail-label and gap-rank permutations, and all rows of the finite real family,
use the same scale. No sign cell, survival condition or selected rank is assumed.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.DominantGap
open BigOperators Cartesian

noncomputable def gapValue {m : ℕ} (p : RawConfig m)
    (w : Option (Fin m)→ℝ) (T : ℝ) : ℝ := ∑ x,w x*gapPoint p T x

def GapDominant {m : ℕ} (p : RawConfig m) (w : Option (Fin m)→ℝ) (g : Fin m) : Prop :=
  Dominant (tailCoefficient p w) (fun k => (p.2 k).val) g

def StableGap {m : ℕ} (p : RawConfig m) (w : Option (Fin m)→ℝ) (T : ℝ) : Prop :=
  (gapValue p w T=0↔∀ a : Fin m,w (some a)=0) ∧
    ∀ g,GapDominant p w g→0<tailCoefficient p w g*gapValue p w T

/-- The same large real T works for every actual tau/rho permutation and every
row in an arbitrary finite family. Zero tests concern actual tail coefficients. -/
theorem finite_gap_family_shared_threshold {κ : Type*} [Fintype κ] {m : ℕ}
    (w : κ→Option (Fin m)→ℝ) :
    ∃ B : ℝ,2≤B ∧ ∀ T : ℝ,B≤T→∀ p : RawConfig m,∀ a,StableGap p (w a) T := by
  classical
  obtain ⟨B,hB,hstable⟩ := finite_family_shared_threshold_varying
    (fun z : RawConfig m×κ => tailCoefficient z.1 (w z.2))
    (fun z : RawConfig m×κ => fun g : Fin m => (z.1.2 g).val)
    (by intro z i j hij; exact z.1.2.injective (Fin.ext hij))
  refine ⟨B,hB,?_⟩
  intro T hT p a
  have h := hstable T hT (p,a)
  have hv : gapValue p (w a) T=
      powerSum (tailCoefficient p (w a)) (fun g => (p.2 g).val) T :=
    weighted_gapPoint_eq_sum p (w a) T
  constructor
  · calc
      gapValue p (w a) T=0 ↔
          powerSum (tailCoefficient p (w a)) (fun g => (p.2 g).val) T=0 := by rw [hv]
      _ ↔ ∀ g,tailCoefficient p (w a) g=0 := h.1
      _ ↔ ∀ b : Fin m,w a (some b)=0 := tailCoefficient_all_zero_iff p (w a)
  · intro g hg
    rw [hv]
    exact h.2 g hg

lemma sign_iff_of_positive_product {a b : ℝ} (h : 0<a*b) :
    (0<b↔0<a) ∧ (b<0↔a<0) := by
  rcases mul_pos_iff.mp h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · constructor
    · exact ⟨fun _ => ha,fun _ => hb⟩
    · constructor <;> intro hn <;> linarith only [ha,hb,hn]
  · constructor
    · constructor <;> intro hp <;> linarith only [ha,hb,hp]
    · exact ⟨fun _ => ha,fun _ => hb⟩

/-- Activation sign is determined by the largest-rank nonzero actual prefix. -/
theorem stableGap_sign_iff {m : ℕ} {p : RawConfig m} {w : Option (Fin m)→ℝ}
    {T : ℝ} (h : StableGap p w T) {g : Fin m} (hg : GapDominant p w g) :
    (0<gapValue p w T↔0<tailCoefficient p w g) ∧
      (gapValue p w T<0↔tailCoefficient p w g<0) :=
  sign_iff_of_positive_product (h.2 g hg)

/-- Under zero-sum, the actual suffix coefficient is exactly the source
anchor-plus-prefix coefficient; no abstract tree/run identification is used. -/
theorem stableGap_prefix_sign_iff {m : ℕ} {p : RawConfig m} {w : Option (Fin m)→ℝ}
    {T : ℝ} (hzero : (∑ x,w x)=0) (h : StableGap p w T)
    {g : Fin m} (hg : GapDominant p w g) :
    (0<gapValue p w T↔0<w none+
      ∑ k in Finset.univ.filter (fun k : Fin m => k.val<g.val),w (some (p.1 k))) ∧
    (gapValue p w T<0↔w none+
      ∑ k in Finset.univ.filter (fun k : Fin m => k.val<g.val),w (some (p.1 k))<0) := by
  simpa only [tailCoefficient_eq_prefix p w hzero g] using stableGap_sign_iff h hg
end MaxCaterpillar.Frontier.RandomRestriction.DominantGap
