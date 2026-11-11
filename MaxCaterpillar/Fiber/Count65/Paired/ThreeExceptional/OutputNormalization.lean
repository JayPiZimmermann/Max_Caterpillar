import MaxCaterpillar.Fiber.Count65.Paired.ThreeExceptional.Profile
import MaxCaterpillar.Fiber.Count65.Paired.PairNormalization
import MaxCaterpillar.Fiber.Count65.Paired.SecondReindex

/-! Opposite physical head outputs normalize by positive scaling. Reversed
head order transports subsequent paths by a genuine reindexing homeomorphism. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.ThreeExceptional
open BigOperators Frontier Absorption

noncomputable def headScales (c : Fin 2 → ℝ) : Fin 5 → ℝ :=
  Fin.append (fun _ : Fin 3 => 1) c

lemma headScales_pos (c : Fin 2 → ℝ) (hc : ∀ i,0<c i) : ∀ i,0<headScales c i := by
  intro i
  fin_cases i
  · change (0:ℝ)<1
    norm_num
  · change (0:ℝ)<1
    norm_num
  · change (0:ℝ)<1
    norm_num
  · exact hc 0
  · exact hc 1

private lemma head_network_ext {a b : Network 4 6 5}
    (hW₁ : a.W₁=b.W₁) (hb₁ : a.b₁=b.b₁) (hW₂ : a.W₂=b.W₂)
    (hb₂ : a.b₂=b.b₂) (hw₃ : a.w₃=b.w₃) (hb₃ : a.b₃=b.b₃) : a=b := by
  apply (networkEquivParameters 4 6 5).injective
  exact Prod.ext hW₁ (Prod.ext hb₁ (Prod.ext hW₂ (Prod.ext hb₂ (Prod.ext hw₃ hb₃))))

/-- Positive scaling changes only the actual last two incoming rows and their
outputs. This equality concerns all six physical parameter arrays. -/
lemma profile_scale_heads (U : Fin 2 → Fin 2 → ℝ) (F G : Fin 6 → ℝ)
    (rows : Fin 2 → Fin 6 → ℝ) (weights c : Fin 2 → ℝ) (b₁ b₂ b₃ : Bool) :
    scaleSecond (profileNet U F G rows weights b₁ b₂ b₃) (headScales c)=
      profileNet U F G (fun k => c k • rows k) (fun k => weights k/c k) b₁ b₂ b₃ := by
  refine head_network_ext
    (a := scaleSecond (profileNet U F G rows weights b₁ b₂ b₃) (headScales c))
    (b := profileNet U F G (fun k => c k • rows k) (fun k => weights k/c k) b₁ b₂ b₃)
    rfl rfl ?_ ?_ ?_ rfl
  · funext i j
    fin_cases i <;> simp [scaleSecond,headScales,profileNet,switchingWithSpectators,
      appendSpectators,Fin.append,Fin.addCases] <;> norm_num
  · funext i
    fin_cases i <;> simp [scaleSecond,headScales,profileNet,switchingWithSpectators,
      appendSpectators,Fin.append,Fin.addCases] <;> norm_num
  · funext i
    fin_cases i <;> simp [scaleSecond,headScales,profileNet,switchingWithSpectators,
      appendSpectators,Fin.append,Fin.addCases] <;> norm_num

lemma profile_heads_swap (U : Fin 2 → Fin 2 → ℝ) (F G P Q : Fin 6 → ℝ)
    (d e : ℝ) (b₁ b₂ b₃ : Bool) :
    reindexSecond (profileNet U F G ![P,Q] ![d,e] b₁ b₂ b₃) (Equiv.swap 3 4)=
      profileNet U F G ![Q,P] ![e,d] b₁ b₂ b₃ := by
  refine head_network_ext
    (a := reindexSecond (profileNet U F G ![P,Q] ![d,e] b₁ b₂ b₃) (Equiv.swap 3 4))
    (b := profileNet U F G ![Q,P] ![e,d] b₁ b₂ b₃)
    rfl rfl ?_ ?_ ?_ rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

/-- Transfer a normalized-head deformation to an arbitrary opposite-sign
physical head profile. The callback is discharged by the normalized theorem;
this helper performs only positive scaling and genuine path transport. -/
theorem opposite_profile_to_unit (U : Fin 2 → Fin 2 → ℝ) (F G : Fin 6 → ℝ)
    (rows : Fin 2 → Fin 6 → ℝ) (weights : Fin 2 → ℝ) (b₁ b₂ b₃ : Bool)
    (hop : (0<weights 0 ∧ weights 1<0) ∨ (weights 0<0 ∧ 0<weights 1))
    (hnet : ∀ x,(profileNet U F G rows weights b₁ b₂ b₃).eval x=Maximum 4 x)
    (normalized : ∀ P Q : Fin 6 → ℝ,
      (∀ x,(profileNet U F G ![P,Q] ![1,-1] b₁ b₂ b₃).eval x=Maximum 4 x) →
      ∃ endpoint : Network 4 6 5,
        JoinedIn (ExactSet 4 6 5) (profileNet U F G ![P,Q] ![1,-1] b₁ b₂ b₃) endpoint ∧
        endpoint.W₁=pairedRows U ∧ endpoint.HasZeroBiases ∧
        (∀ x,endpoint.eval x=Maximum 4 x) ∧ endpoint.w₃ 0=1 ∧
        endpoint.W₂ 0=(if b₁ then -comparisonRow U else comparisonRow U)) :
    ∃ endpoint : Network 4 6 5,
      JoinedIn (ExactSet 4 6 5) (profileNet U F G rows weights b₁ b₂ b₃) endpoint ∧
      endpoint.W₁=pairedRows U ∧ endpoint.HasZeroBiases ∧
      (∀ x,endpoint.eval x=Maximum 4 x) ∧ endpoint.w₃ 0=1 ∧
      endpoint.W₂ 0=(if b₁ then -comparisonRow U else comparisonRow U) := by
  let source := profileNet U F G rows weights b₁ b₂ b₃
  let a : ExactFiber 4 6 5 := ⟨source,hnet⟩
  rcases hop with ⟨hd,he⟩ | ⟨hd,he⟩
  · let c : Fin 2 → ℝ := ![weights 0,-weights 1]
    have hc : ∀ i,0<c i := by
      intro i
      fin_cases i
      · exact hd
      · exact neg_pos.mpr he
    have hp : JoinedIn (ExactSet 4 6 5) source (scaleSecond source (headScales c)) :=
      ⟨(scaleSecondPath (headScales c) (headScales_pos c hc) a).map continuous_subtype_val,
        fun t => (scaleSecondPath (headScales c) (headScales_pos c hc) a t).property⟩
    have hr : (fun k => c k • rows k)=![weights 0 • rows 0,(-weights 1) • rows 1] := by
      funext i
      fin_cases i <;> rfl
    have hw : (fun k => weights k/c k)=(![1,-1] : Fin 2 → ℝ) := by
      funext i
      fin_cases i <;> simp [c,hd.ne',he.ne]
    rw [profile_scale_heads,hr,hw] at hp
    obtain ⟨E,hE,hfirst,hbias,hexact,hout,hrow⟩ := normalized _ _ hp.target_mem
    exact ⟨E,hp.trans hE,hfirst,hbias,hexact,hout,hrow⟩
  · let c : Fin 2 → ℝ := ![-weights 0,weights 1]
    have hc : ∀ i,0<c i := by
      intro i
      fin_cases i
      · exact neg_pos.mpr hd
      · exact he
    have hp : JoinedIn (ExactSet 4 6 5) source (scaleSecond source (headScales c)) :=
      ⟨(scaleSecondPath (headScales c) (headScales_pos c hc) a).map continuous_subtype_val,
        fun t => (scaleSecondPath (headScales c) (headScales_pos c hc) a t).property⟩
    have hr : (fun k => c k • rows k)=![(-weights 0) • rows 0,weights 1 • rows 1] := by
      funext i
      fin_cases i <;> rfl
    have hw : (fun k => weights k/c k)=(![-1,1] : Fin 2 → ℝ) := by
      funext i
      fin_cases i <;> simp [c,hd.ne,he.ne']
    rw [profile_scale_heads,hr,hw] at hp
    let normal := profileNet U F G ![weights 1 • rows 1,(-weights 0) • rows 0]
      ![1,-1] b₁ b₂ b₃
    have hn : ∀ x,normal.eval x=Maximum 4 x := by
      intro x
      have hs := hp.target_mem x
      rw [← profile_heads_swap U F G _ _ 1 (-1) b₁ b₂ b₃,reindexSecond_eval] at hs
      exact hs
    obtain ⟨E,hE,hfirst,hbias,hexact,hout,hrow⟩ := normalized _ _ hn
    have ht := joinedIn_reindexSecond hE (Equiv.swap (3 : Fin 5) 4)
    rw [profile_heads_swap] at ht
    refine ⟨reindexSecond E (Equiv.swap 3 4),hp.trans ht,hfirst,
      reindexSecond_zeroBiases E _ hbias,?_,?_,?_⟩
    · intro x
      rw [reindexSecond_eval]
      exact hexact x
    · change E.w₃ ((Equiv.swap (3 : Fin 5) 4) 0)=1
      convert hout using 1
    · change E.W₂ ((Equiv.swap (3 : Fin 5) 4) 0)=_
      convert hrow using 1

end MaxCaterpillar.Fiber.Count65.Paired.ThreeExceptional
