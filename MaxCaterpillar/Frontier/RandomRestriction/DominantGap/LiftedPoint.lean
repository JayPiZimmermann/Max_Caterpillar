import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.GapPolynomial
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Directional

/-! # The Cartesian gap polynomial in the actual N-coordinate model

The tail embedding is an arbitrary actual coordinate embedding. Coordinates
outside its image are tied at zero; their original row weights are collected
at the anchor. No survival or rational-weight assumption enters the bridge.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.DominantGap
open BigOperators
open Cartesian

/-- The actual original-coordinate point, using the model's proved zero lift. -/
noncomputable def actualGapPoint {N m : ℕ} (e : Fin m ↪ Fin N)
    (p : RawConfig m) (T : ℝ) : Point N :=
  NormalizedNetwork.lift e (fun a => gapPoint p T (some a))

/-- The tied selected block contributes its complete original row-weight sum
at the anchor, while every tail coefficient remains its original coefficient. -/
noncomputable def collapsedRow {N m : ℕ} (e : Fin m ↪ Fin N)
    (w : Point N) : Option (Fin m)→ℝ
  | none => ∑ i in Finset.univ.filter (fun i : Fin N => i∉Finset.univ.image e),w i
  | some a => w (e a)

/-- The scalar form on the actual point is exactly the original Cartesian
anchor-and-tail expansion for the collapsed original row. -/
theorem lin_actualGapPoint_eq_weighted {N m : ℕ} (e : Fin m ↪ Fin N)
    (p : RawConfig m) (w : Point N) (T : ℝ) :
    lin w (actualGapPoint e p T)=
      ∑ x : Option (Fin m),collapsedRow e w x*gapPoint p T x := by
  rw [actualGapPoint,NormalizedNetwork.lin_lift,Fintype.sum_option]
  change (∑ a : Fin m,w (e a)*gapPoint p T (some a))=
    collapsedRow e w none*0+∑ a : Fin m,w (e a)*gapPoint p T (some a)
  rw [mul_zero,zero_add]

/-- The actual original-coordinate form has the exact distinct-power gap expansion. -/
theorem lin_actualGapPoint_eq_sum {N m : ℕ} (e : Fin m ↪ Fin N)
    (p : RawConfig m) (w : Point N) (T : ℝ) :
    lin w (actualGapPoint e p T)=
      ∑ g : Fin m,tailCoefficient p (collapsedRow e w) g*T^((p.2 g).val) := by
  rw [lin_actualGapPoint_eq_weighted,weighted_gapPoint_eq_sum]

/-- Collapsing the actual tied block preserves the complete row sum exactly. -/
theorem collapsedRow_total_sum {N m : ℕ} (e : Fin m ↪ Fin N) (w : Point N) :
    (∑ x : Option (Fin m),collapsedRow e w x)=∑ i : Fin N,w i := by
  classical
  have hi : (∑ i in Finset.univ.image e,w i)=∑ a : Fin m,w (e a) := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact e.injective hab
  have hf : Finset.univ.filter (fun i : Fin N => i∈Finset.univ.image e)=
      Finset.univ.image e := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have hp := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin N))
    (fun i => i∈Finset.univ.image e) w
  rw [hf,hi] at hp
  rw [Fintype.sum_option]
  change (∑ i in Finset.univ.filter (fun i : Fin N => i∉Finset.univ.image e),w i)+
      (∑ a : Fin m,w (e a))=∑ i : Fin N,w i
  linarith only [hp]

theorem collapsedRow_zero_sum {N m : ℕ} (e : Fin m ↪ Fin N) (w : Point N)
    (hzero : (∑ i : Fin N,w i)=0) :
    (∑ x : Option (Fin m),collapsedRow e w x)=0 := by
  rw [collapsedRow_total_sum,hzero]

/-- Tail vanishing is the model's actual restricted coefficient row vanishing. -/
theorem collapsedRow_tail_zero_iff_restrict {N m : ℕ} (e : Fin m ↪ Fin N) (w : Point N) :
    (∀ a : Fin m,collapsedRow e w (some a)=0) ↔ NormalizedNetwork.restrict e w=0 := by
  constructor
  · intro H
    funext a
    exact H a
  · intro H a
    exact congrFun H a

/-- This coefficient criterion is equivalent to actual restriction vanishing,
with no zero-sum assumption on the original row. -/
theorem tailCoefficient_collapsed_zero_iff {N m : ℕ} (e : Fin m ↪ Fin N)
    (p : RawConfig m) (w : Point N) :
    (∀ g : Fin m,tailCoefficient p (collapsedRow e w) g=0) ↔
      NormalizedNetwork.restrict e w=0 :=
  (tailCoefficient_all_zero_iff p (collapsedRow e w)).trans
    (collapsedRow_tail_zero_iff_restrict e w)

theorem gapPolynomial_collapsed_eval {N m : ℕ} (e : Fin m ↪ Fin N)
    (p : RawConfig m) (w : Point N) (T : ℝ) :
    (gapPolynomial p (collapsedRow e w)).eval T=lin w (actualGapPoint e p T) := by
  rw [gapPolynomial_eval,lin_actualGapPoint_eq_weighted]

theorem gapPolynomial_collapsed_eq_zero_iff {N m : ℕ} (e : Fin m ↪ Fin N)
    (p : RawConfig m) (w : Point N) :
    gapPolynomial p (collapsedRow e w)=0 ↔ NormalizedNetwork.restrict e w=0 :=
  (gapPolynomial_eq_zero_iff p (collapsedRow e w)).trans
    (collapsedRow_tail_zero_iff_restrict e w)

/-- Every coordinate of the actual chosen tail has its original Cartesian gap value. -/
theorem actualGapPoint_selected {N m : ℕ} (e : Fin m ↪ Fin N)
    (p : RawConfig m) (T : ℝ) (a : Fin m) :
    actualGapPoint e p T (e a)=gapPoint p T (some a) :=
  NormalizedNetwork.lift_selected e _ a

/-- The actual complementary block is tied at zero. -/
theorem actualGapPoint_outside {N m : ℕ} (e : Fin m ↪ Fin N)
    (p : RawConfig m) (T : ℝ) (i : Fin N) (hi : i∉Finset.univ.image e) :
    actualGapPoint e p T i=0 :=
  NormalizedNetwork.lift_outside e _ i hi

/-- Every tail gap coordinate is strictly below the tied block for T>0. -/
theorem actualGapPoint_selected_neg {N m : ℕ} (e : Fin m ↪ Fin N)
    (p : RawConfig m) (T : ℝ) (hT : 0<T) (a : Fin m) :
    actualGapPoint e p T (e a)<0 := by
  rw [actualGapPoint_selected]
  change -(∑ g in Finset.univ.filter (fun g : Fin m => g.val≤(p.1.symm a).val),
    T^((p.2 g).val))<0
  have hs : 0<∑ g in Finset.univ.filter (fun g : Fin m => g.val≤(p.1.symm a).val),
      T^((p.2 g).val) := by
    apply Finset.sum_pos'
    · intro g _
      exact (pow_pos hT _).le
    · exact ⟨p.1.symm a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_rfl⟩,pow_pos hT _⟩
  linarith only [hs]
end MaxCaterpillar.Frontier.RandomRestriction.DominantGap
