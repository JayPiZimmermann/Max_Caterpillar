import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

/-! # Exact two-label forcing by position transpositions

The construction acts on ordinary permutations. Its inverse retains the two
original source positions, yielding an actual equivalence with each pinned
permutation and a uniform set of source choices.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias

variable {V : Type*} [DecidableEq V]

def firstSource (τ : Equiv.Perm V) (a : V) : V := τ.symm a

def firstForced (τ : Equiv.Perm V) (p a : V) : Equiv.Perm V :=
  (Equiv.swap p (firstSource τ a)).trans τ

def secondSource (τ : Equiv.Perm V) (p a b : V) : V :=
  (firstForced τ p a).symm b

def forcePair (τ : Equiv.Perm V) (p q a b : V) : Equiv.Perm V :=
  (Equiv.swap q (secondSource τ p a b)).trans (firstForced τ p a)

theorem firstForced_apply_pin (τ : Equiv.Perm V) (p a : V) :
    firstForced τ p a p = a := by
  simp [firstForced,firstSource,Equiv.trans_apply]

theorem firstSource_after_undo (σ : Equiv.Perm V) (p a r : V)
    (hσ : σ p = a) : firstSource ((Equiv.swap p r).trans σ) a = r := by
  have hi : σ.symm a = p := by
    apply σ.injective
    simpa only [σ.apply_symm_apply] using hσ.symm
  change Equiv.swap p r (σ.symm a) = r
  rw [hi,Equiv.swap_apply_left]

/-- One label is forced by swapping its actual source with its desired slot.
The inverse performs the same position swap, using the retained source. -/
def oneLabelEquiv (p a : V) : Equiv.Perm V ≃
    {σ : Equiv.Perm V // σ p = a} × V where
  toFun τ := (⟨firstForced τ p a,firstForced_apply_pin τ p a⟩,firstSource τ a)
  invFun z := (Equiv.swap p z.2).trans z.1.val
  left_inv τ := by
    ext x
    change τ (Equiv.swap p (firstSource τ a) (Equiv.swap p (firstSource τ a) x)) = τ x
    rw [Equiv.swap_apply_self]
  right_inv := by
    rintro ⟨⟨σ,hσ⟩,r⟩
    have hr := firstSource_after_undo σ p a r hσ
    apply Prod.ext
    · apply Subtype.ext
      ext x
      change σ (Equiv.swap p r
        (Equiv.swap p (firstSource ((Equiv.swap p r).trans σ) a) x)) = σ x
      rw [hr,Equiv.swap_apply_self]
    · exact hr

theorem source_ne_p_of_pinned (σ : Equiv.Perm V) (p a b : V)
    (hσ : σ p = a) (hab : a ≠ b) : σ.symm b ≠ p := by
  intro he
  have hh := congrArg σ he
  simp only [σ.apply_symm_apply,hσ] at hh
  exact hab hh.symm

/-- Forcing the second distinct label does not disturb the first pinned slot.
The second retained source is any position other than the first slot. -/
def secondLabelEquiv (p q a b : V) (hpq : p ≠ q) (hab : a ≠ b) :
    {σ : Equiv.Perm V // σ p = a} ≃
      {σ : Equiv.Perm V // σ p = a ∧ σ q = b} × {s : V // s ≠ p} where
  toFun σ :=
    (⟨firstForced σ.val q b,by
      constructor
      · change σ.val (Equiv.swap q (σ.val.symm b) p) = a
        rw [Equiv.swap_apply_of_ne_of_ne hpq
          (source_ne_p_of_pinned σ.val p a b σ.property hab).symm]
        exact σ.property
      · exact firstForced_apply_pin σ.val q b⟩,
     ⟨σ.val.symm b,source_ne_p_of_pinned σ.val p a b σ.property hab⟩)
  invFun z := ⟨(Equiv.swap q z.2.val).trans z.1.val,by
    change z.1.val (Equiv.swap q z.2.val p) = a
    rw [Equiv.swap_apply_of_ne_of_ne hpq z.2.property.symm]
    exact z.1.property.1⟩
  left_inv σ := by
    apply Subtype.ext
    ext x
    change σ.val (Equiv.swap q (σ.val.symm b) (Equiv.swap q (σ.val.symm b) x)) = σ.val x
    rw [Equiv.swap_apply_self]
  right_inv := by
    rintro ⟨⟨σ,hσ⟩,⟨s,hs⟩⟩
    have hr := firstSource_after_undo σ q b s hσ.2
    apply Prod.ext
    · apply Subtype.ext
      ext x
      change σ (Equiv.swap q s
        (Equiv.swap q (firstSource ((Equiv.swap q s).trans σ) b) x)) = σ x
      rw [hr,Equiv.swap_apply_self]
    · apply Subtype.ext
      exact hr

private def sourceShuffle (p q a b : V) :
    ({σ : Equiv.Perm V // σ p = a ∧ σ q = b} × {s : V // s ≠ p}) × V ≃
      {σ : Equiv.Perm V // σ p = a ∧ σ q = b} × (V × {s : V // s ≠ p}) where
  toFun z := (z.1.1,(z.2,z.1.2))
  invFun z := ((z.1,z.2.2),z.2.1)
  left_inv := by rintro ⟨⟨σ,s⟩,r⟩; rfl
  right_inv := by rintro ⟨σ,r,s⟩; rfl

/-- Exact forcing bijection. The source positions are not independent extra
randomness: they are retained from the original permutation, and undo the
second swap followed by the first. -/
def forcingEquiv (p q a b : V) (hpq : p ≠ q) (hab : a ≠ b) :
    Equiv.Perm V ≃
      {σ : Equiv.Perm V // σ p = a ∧ σ q = b} × (V × {s : V // s ≠ p}) :=
  ((oneLabelEquiv p a).trans
    ((secondLabelEquiv p q a b hpq hab).prodCongr (Equiv.refl V))).trans
      (sourceShuffle p q a b)

theorem forcingEquiv_fst (p q a b : V) (hpq : p ≠ q) (hab : a ≠ b)
    (τ : Equiv.Perm V) :
    ((forcingEquiv p q a b hpq hab τ).1).val = forcePair τ p q a b := rfl

theorem forcingEquiv_firstSource (p q a b : V) (hpq : p ≠ q) (hab : a ≠ b)
    (τ : Equiv.Perm V) :
    (forcingEquiv p q a b hpq hab τ).2.1 = firstSource τ a := rfl

theorem forcingEquiv_secondSource (p q a b : V) (hpq : p ≠ q) (hab : a ≠ b)
    (τ : Equiv.Perm V) :
    ((forcingEquiv p q a b hpq hab τ).2.2).val = secondSource τ p a b := rfl

theorem secondSource_ne_first_position (τ : Equiv.Perm V) (p a b : V)
    (hab : a ≠ b) : secondSource τ p a b ≠ p :=
  source_ne_p_of_pinned (firstForced τ p a) p a b (firstForced_apply_pin τ p a) hab

theorem forcePair_pins (τ : Equiv.Perm V) (p q a b : V)
    (hpq : p ≠ q) (hab : a ≠ b) :
    forcePair τ p q a b p = a ∧ forcePair τ p q a b q = b :=
  ((forcingEquiv p q a b hpq hab τ).1).property

theorem forcePair_apply (τ : Equiv.Perm V) (p q a b x : V) :
    forcePair τ p q a b x =
      τ (Equiv.swap p (firstSource τ a) (Equiv.swap q (secondSource τ p a b) x)) := rfl

/-- Only the four actual position slots in the two transpositions can change. -/
theorem forcePair_apply_away (τ : Equiv.Perm V) (p q a b x : V)
    (hxp : x ≠ p) (hxq : x ≠ q) (hxr : x ≠ firstSource τ a)
    (hxs : x ≠ secondSource τ p a b) : forcePair τ p q a b x = τ x := by
  rw [forcePair_apply,Equiv.swap_apply_of_ne_of_ne hxq hxs,
    Equiv.swap_apply_of_ne_of_ne hxp hxr]

/-- Every conditional output has exactly the same explicit source fiber. -/
def forcingFiberEquiv (p q a b : V) (hpq : p ≠ q) (hab : a ≠ b)
    (σ : {σ : Equiv.Perm V // σ p = a ∧ σ q = b}) :
    {τ : Equiv.Perm V // forcePair τ p q a b = σ.val} ≃ (V × {s : V // s ≠ p}) where
  toFun τ := (forcingEquiv p q a b hpq hab τ.val).2
  invFun z := ⟨(forcingEquiv p q a b hpq hab).symm (σ,z),by
    have hh := congrArg (fun w => w.1.val)
      ((forcingEquiv p q a b hpq hab).apply_symm_apply (σ,z))
    exact hh⟩
  left_inv τ := by
    apply Subtype.ext
    apply (forcingEquiv p q a b hpq hab).injective
    rw [(forcingEquiv p q a b hpq hab).apply_symm_apply]
    apply Prod.ext
    · apply Subtype.ext
      exact τ.property.symm
    · rfl
  right_inv z := by
    exact congrArg Prod.snd ((forcingEquiv p q a b hpq hab).apply_symm_apply (σ,z))

theorem forcing_preimage_card [Fintype V] (p q a b : V)
    (hpq : p ≠ q) (hab : a ≠ b)
    (σ : {σ : Equiv.Perm V // σ p = a ∧ σ q = b}) :
    Fintype.card {τ : Equiv.Perm V // forcePair τ p q a b = σ.val} =
      Fintype.card V * (Fintype.card V - 1) := by
  classical
  rw [Fintype.card_congr (forcingFiberEquiv p q a b hpq hab σ),Fintype.card_prod]
  have hc : Fintype.card {s : V // s ≠ p} = Fintype.card V - 1 := by
    simpa using Fintype.card_subtype_compl (fun s : V => s = p)
  rw [hc]

#check @forcingEquiv
#check @forcePair_apply_away
#print axioms forcingEquiv
#print axioms forcingEquiv_fst
#print axioms forcePair_pins
#print axioms forcePair_apply_away
#print axioms forcingFiberEquiv
#print axioms forcing_preimage_card
end MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias
