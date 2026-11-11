import MaxCaterpillar.Frontier.RandomRestriction.ConfigurationsGeometry

/-! # Exact finite counts for three-permutation configurations

Every literal full/rank event has exactly one free tail-permutation factor.
For fixed full and rank coordinates, the actual finite fiber is explicitly
equivalent to the entire tail-permutation space. No conditional law is assumed. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.Configurations
open BigOperators

noncomputable def equivEvent {α β : Type*} [Fintype α]
    (e : α ≃ β) (B : Finset β) : Finset α := by
  classical
  exact Finset.univ.filter (fun a => e a ∈ B)

lemma equivEvent_card {α β : Type*} [Fintype α] (e : α ≃ β) (B : Finset β) :
    (equivEvent e B).card=B.card := by
  classical
  have himage : (equivEvent e B).image e=B := by
    ext b
    constructor
    · rintro hb
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
      exact (Finset.mem_filter.mp ha).2
    · intro hb
      refine Finset.mem_image.mpr ⟨e.symm b,?_,e.apply_symm_apply b⟩
      simpa only [equivEvent,Finset.mem_filter,Finset.mem_univ,true_and,
        Equiv.apply_symm_apply] using hb
  calc
    _ = ((equivEvent e B).image e).card :=
      (Finset.card_image_of_injective _ e.injective).symm
    _ = B.card := congrArg Finset.card himage

variable {m : ℕ}

/-- Literal pullback of any full/rank event to the actual three-permutation space. -/
noncomputable def pullbackEvent (B : Finset (LiteralConfiguration m)) :
    Finset (Configuration m) := by
  classical
  exact Finset.univ.filter (fun ω => effectiveConfiguration ω ∈ B)

@[simp] lemma mem_pullbackEvent (B : Finset (LiteralConfiguration m)) (ω : Configuration m) :
    ω ∈ pullbackEvent B ↔ effectiveConfiguration ω ∈ B := by
  classical
  simp only [pullbackEvent,Finset.mem_filter,Finset.mem_univ,true_and]

/-- An explicit bijection of the actual event subtype with a free tail
permutation and the original literal event subtype. -/
noncomputable def pullbackEventEquiv (B : Finset (LiteralConfiguration m)) :
    ↥(pullbackEvent B) ≃ TailPerm m × ↥B where
  toFun ω := (ω.val.2.1,⟨effectiveConfiguration ω.val,(mem_pullbackEvent B ω.val).mp ω.property⟩)
  invFun p := ⟨(configurationEquiv m).symm (p.1,p.2.val),
    (mem_pullbackEvent B _).mpr (by
      have he := congrArg Prod.snd ((configurationEquiv m).apply_symm_apply (p.1,p.2.val))
      change effectiveConfiguration ((configurationEquiv m).symm (p.1,p.2.val))=p.2.val at he
      rw [he]
      exact p.2.property)⟩
  left_inv ω := by
    apply Subtype.ext
    exact (configurationEquiv m).symm_apply_apply ω.val
  right_inv p := by
    have he := (configurationEquiv m).apply_symm_apply (p.1,p.2.val)
    apply Prod.ext
    · change ((configurationEquiv m) ((configurationEquiv m).symm (p.1,p.2.val))).1=p.1
      exact congrArg Prod.fst he
    · apply Subtype.ext
      change ((configurationEquiv m) ((configurationEquiv m).symm (p.1,p.2.val))).2=p.2.val
      exact congrArg Prod.snd he

lemma pullbackEvent_card (B : Finset (LiteralConfiguration m)) :
    (pullbackEvent B).card=Fintype.card (TailPerm m)*B.card := by
  calc
    _ = Fintype.card ↥(pullbackEvent B) := (Fintype.card_coe _).symm
    _ = Fintype.card (TailPerm m × ↥B) := Fintype.card_congr (pullbackEventEquiv B)
    _ = _ := by rw [Fintype.card_prod,Fintype.card_coe]

lemma card_configuration (m : ℕ) :
    Fintype.card (Configuration m)=
      Fintype.card (TailPerm m)*Fintype.card (LiteralConfiguration m) := by
  calc
    _ = Fintype.card (TailPerm m × LiteralConfiguration m) :=
      Fintype.card_congr (configurationEquiv m)
    _ = _ := Fintype.card_prod _ _

/-- The literal event fraction is unchanged on the enlarged actual sample space. -/
lemma pullbackEvent_fraction (B : Finset (LiteralConfiguration m)) :
    ((pullbackEvent B).card:ℝ)/(Fintype.card (Configuration m):ℝ)=
      (B.card:ℝ)/(Fintype.card (LiteralConfiguration m):ℝ) := by
  rw [pullbackEvent_card,card_configuration]
  simp only [Nat.cast_mul]
  apply mul_div_mul_left
  exact_mod_cast (Fintype.card_ne_zero : Fintype.card (TailPerm m) ≠ 0)

/-- The actual finite configuration fiber obtained by fixing σ and ρ. -/
abbrev FixedOuter (σ : FullPerm m) (ρ : RankPerm m) :=
  {ω : Configuration m // ω.1=σ ∧ ω.2.2=ρ}

def fixedOuterEquiv (σ : FullPerm m) (ρ : RankPerm m) :
    TailPerm m ≃ FixedOuter σ ρ where
  toFun τ := ⟨(σ,(τ,ρ)),rfl,rfl⟩
  invFun ω := ω.val.2.1
  left_inv _ := rfl
  right_inv ω := by
    apply Subtype.ext
    exact Prod.ext ω.property.1.symm (Prod.ext rfl ω.property.2.symm)

lemma card_fixedOuter (σ : FullPerm m) (ρ : RankPerm m) :
    Fintype.card (FixedOuter σ ρ)=Fintype.card (TailPerm m) :=
  Fintype.card_congr (fixedOuterEquiv σ ρ).symm

/-- Pulling back any literal tail event inside that actual fiber preserves its count. -/
noncomputable def fixedOuterEvent (σ : FullPerm m) (ρ : RankPerm m)
    (A : Finset (TailPerm m)) : Finset (FixedOuter σ ρ) :=
  equivEvent (fixedOuterEquiv σ ρ).symm A

lemma fixedOuterEvent_card (σ : FullPerm m) (ρ : RankPerm m) (A : Finset (TailPerm m)) :
    (fixedOuterEvent σ ρ A).card=A.card := equivEvent_card _ _

/-- Exact conditional finite averaging: σ and ρ are fixed parameters while τ
runs through every tail permutation once. This also holds for m=0. -/
lemma sum_fixedOuter (σ : FullPerm m) (ρ : RankPerm m) (f : TailPerm m → ℝ) :
    (∑ ω : FixedOuter σ ρ,f ω.val.2.1)=∑ τ,f τ := by
  have h := Equiv.sum_comp (fixedOuterEquiv σ ρ) (fun ω : FixedOuter σ ρ => f ω.val.2.1)
  exact h.symm

lemma average_fixedOuter (σ : FullPerm m) (ρ : RankPerm m) (f : TailPerm m → ℝ) :
    (∑ ω : FixedOuter σ ρ,f ω.val.2.1)/(Fintype.card (FixedOuter σ ρ):ℝ)=
      (∑ τ,f τ)/(Fintype.card (TailPerm m):ℝ) := by
  rw [sum_fixedOuter,card_fixedOuter]

/-- Exact product summation with the independent tail permutation innermost. -/
lemma sum_configuration_by_outer (f : Configuration m → ℝ) :
    (∑ ω,f ω)=∑ σ : FullPerm m,∑ ρ : RankPerm m,∑ τ : TailPerm m,f (σ,(τ,ρ)) := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro σ _
  exact Finset.sum_comm

end MaxCaterpillar.Frontier.RandomRestriction.Configurations
