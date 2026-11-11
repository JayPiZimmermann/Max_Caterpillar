import MaxCaterpillar.Fiber.Mixed65.Heads
import MaxCaterpillar.Fiber.Components
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Clopen

/-!
# Topology of the two physical translation heads

The parameter space contains the four physical translation coefficients and two
actual intercepts in a specified invariant function subspace. Its topology is the
ordinary product/subspace topology. The nonpaired network classification must
separately extract these heads and prove the invariant function space is clipping
rigid. No extraction hypothesis is hidden in this file's definitions.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.HeadTopology
open BigOperators Set Function MaxCaterpillar.Frontier MaxCaterpillar.Fiber.Mixed65

variable {α : Type*}

/-- Affine interpolation of the six fields of a physical head pair. -/
noncomputable def combine (a b : ℝ) (h k : Heads α) : Heads α :=
  ⟨a*h.a+b*k.a, a*h.b+b*k.b, a*h.c+b*k.c, a*h.d+b*k.d,
    fun x => a*h.A x+b*k.A x, fun x => a*h.B x+b*k.B x⟩

lemma combine_signed {h k : Heads α} {L : α → ℝ}
    (hh : h.IsSigned L) (hk : k.IsSigned L)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    (combine a b h k).IsSigned L := by
  rcases hh with ⟨hA,hB,ha1,hd1,hb0,hc0,hbp,hcn⟩
  rcases hk with ⟨kA,kB,ka1,kd1,kb0,kc0,kbp,kcn⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · funext x
    simp only [combine,hA,kA]
    rw [← add_mul,hab,one_mul]
  · funext x
    simp only [combine,hB,kB]
    rw [← add_mul,hab,one_mul]
  · simp only [combine,ha1,ka1,mul_one]
    exact hab
  · simp only [combine,hd1,kd1,mul_one]
    exact hab
  · exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hb0)
      (mul_nonpos_of_nonneg_of_nonpos hb kb0)
  · exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hc0)
      (mul_nonpos_of_nonneg_of_nonpos hb kc0)
  · intro hp
    simp only [combine,hbp hp,kbp hp]
    nlinarith only [hab]
  · intro hn
    simp only [combine,hcn hn,kcn hn]
    nlinarith only [hab]

lemma combine_split {h k : Heads α} {L : α → ℝ}
    (hh : h.IsSplit L) (hk : k.IsSplit L)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    (combine a b h k).IsSplit L := by
  rcases hh with ⟨ha1,hd1,hb0,hc0,hA,hB,hL⟩
  rcases hk with ⟨ka1,kd1,kb0,kc0,kA,kB,kL⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · change a*h.a+b*k.a = 1+(a*h.c+b*k.c)
    rw [ha1,ka1]
    nlinarith only [hab]
  · change a*h.d+b*k.d = 1+(a*h.b+b*k.b)
    rw [hd1,kd1]
    nlinarith only [hab]
  · exact add_nonneg (mul_nonneg ha hb0) (mul_nonneg hb kb0)
  · exact add_nonneg (mul_nonneg ha hc0) (mul_nonneg hb kc0)
  · intro x
    exact add_nonneg (mul_nonneg ha (hA x)) (mul_nonneg hb (kA x))
  · intro x
    exact add_nonneg (mul_nonneg ha (hB x)) (mul_nonneg hb (kB x))
  · intro x
    change a*h.A x+b*k.A x-(a*h.B x+b*k.B x)=L x
    calc
      _ = a*(h.A x-h.B x)+b*(k.A x-k.B x) := by ring
      _ = a*L x+b*L x := by rw [hL x,kL x]
      _ = L x := by rw [← add_mul,hab,one_mul]

/-- Shrink only the cross coefficients; the intercept functions stay fixed. -/
noncomputable def shrink (s : ℝ) (h : Heads α) : Heads α :=
  ⟨1+s*(h.a-1),s*h.b,s*h.c,1+s*(h.d-1),h.A,h.B⟩

lemma shrink_split {h : Heads α} {L : α → ℝ} (hh : h.IsSplit L)
    {s : ℝ} (hs : 0 ≤ s) : (shrink s h).IsSplit L := by
  rcases hh with ⟨ha,hd,hb,hc,hA,hB,hL⟩
  refine ⟨?_,?_,mul_nonneg hs hb,mul_nonneg hs hc,hA,hB,hL⟩
  · change 1+s*(h.a-1)=1+s*h.c
    rw [ha]
    ring
  · change 1+s*(h.d-1)=1+s*h.b
    rw [hd]
    ring

lemma shrink_positiveHybrid {h : Heads α} {L : α → ℝ}
    (hh : h.IsPositiveHybrid L) {s : ℝ} (hs : 0 ≤ s) :
    (shrink s h).IsPositiveHybrid L := by
  rcases hh with ⟨hA,hB,ha,hd,hb,hc,hL⟩
  refine ⟨hA,hB,?_,?_,mul_nonneg hs hb,
    mul_nonpos_of_nonneg_of_nonpos hs hc,hL⟩
  · change 1+s*(h.a-1)=1
    rw [ha]
    ring
  · change 1+s*(h.d-1)=1+s*h.b
    rw [hd]
    ring

lemma shrink_negativeHybrid {h : Heads α} {L : α → ℝ}
    (hh : h.IsNegativeHybrid L) {s : ℝ} (hs : 0 ≤ s) :
    (shrink s h).IsNegativeHybrid L := by
  rcases hh with ⟨hA,hB,ha,hd,hb,hc,hL⟩
  refine ⟨hA,hB,?_,?_,mul_nonpos_of_nonneg_of_nonpos hs hb,
    mul_nonneg hs hc,hL⟩
  · change 1+s*(h.a-1)=1+s*h.c
    rw [ha]
    ring
  · change 1+s*(h.d-1)=1
    rw [hd]
    ring

lemma shrink_splitHybrid {h : Heads α} {L : α → ℝ}
    (hh : h.IsSplitHybrid L) {s : ℝ} (hs : 0 ≤ s) :
    (shrink s h).IsSplitHybrid L := by
  rcases hh with hh | hh | hh
  · exact Or.inl (shrink_split hh hs)
  · exact Or.inr (Or.inl (shrink_positiveHybrid hh hs))
  · exact Or.inr (Or.inr (shrink_negativeHybrid hh hs))

lemma shrink_zero_isSplit {h : Heads α} {L : α → ℝ}
    (hh : h.IsSplitHybrid L) : (shrink 0 h).IsSplit L := by
  obtain ⟨hA,hB⟩ := hh.intercepts_nonneg
  have hL : ∀ x, h.A x-h.B x=L x := by
    rcases hh with hh | hh | hh
    · exact hh.2.2.2.2.2.2
    · intro x
      simp only [hh.1,hh.2.1,Pi.zero_apply,sub_zero]
    · intro x
      simp only [hh.1,hh.2.1,Pi.zero_apply,zero_sub,neg_neg]
  exact ⟨by simp [shrink],by simp [shrink],by simp [shrink],by simp [shrink],hA,hB,hL⟩

/-- Ordinary scalar coefficients together with the two invariant intercepts. -/
abbrev Data (E : Submodule ℝ (α → ℝ)) := (Fin 4 → ℝ) × E × E

noncomputable def toHeads {E : Submodule ℝ (α → ℝ)} (p : Data E) : Heads α :=
  ⟨p.1 0,p.1 1,p.1 2,p.1 3,p.2.1,p.2.2⟩

noncomputable def signedPoint (E : Submodule ℝ (α → ℝ)) (L : E) : Data E :=
  (![1,-1,-1,1],L,-L)

lemma toHeads_signedPoint (E : Submodule ℝ (α → ℝ)) (L : E) :
    toHeads (signedPoint E L) = signedHeads (L : α → ℝ) := rfl

/-- The signed component is convex in the actual head coefficients/intercepts. -/
theorem convex_signed (E : Submodule ℝ (α → ℝ)) (L : E) :
    Convex ℝ {p : Data E | (toHeads p).IsSigned (L : α → ℝ)} := by
  intro p hp q hq a b ha hb hab
  have hc := combine_signed hp hq ha hb hab
  convert hc using 1

/-- The split component before its hybrid attachments is convex. -/
theorem convex_split (E : Submodule ℝ (α → ℝ)) (L : E) :
    Convex ℝ {p : Data E | (toHeads p).IsSplit (L : α → ℝ)} := by
  intro p hp q hq a b ha hb hab
  have hc := combine_split hp hq ha hb hab
  convert hc using 1

/-- Canonical split heads for a nonnegative decomposition of the remainder. -/
noncomputable def splitPoint (E : Submodule ℝ (α → ℝ)) (A B : E) : Data E :=
  (![1,0,0,1],A,B)

lemma splitPoint_isSplit (E : Submodule ℝ (α → ℝ)) (L A B : E)
    (hA : ∀ x, 0 ≤ (A : α → ℝ) x) (hB : ∀ x, 0 ≤ (B : α → ℝ) x)
    (hL : A-B=L) : (toHeads (splitPoint E A B)).IsSplit (L : α → ℝ) := by
  have he : (fun x => (A : α → ℝ) x-(B : α → ℝ) x)=(L : α → ℝ) := by
    funext x
    exact congrArg (fun v : E => (v : α → ℝ) x) hL
  change (splitHeads (A : α → ℝ) (B : α → ℝ)).IsSplit (L : α → ℝ)
  rw [← he]
  exact splitHeads_isSplit _ _ hA hB

/-- The signed physical-head coefficient family is path connected. -/
theorem isPathConnected_signed (E : Submodule ℝ (α → ℝ)) (L : E) :
    IsPathConnected {p : Data E | (toHeads p).IsSigned (L : α → ℝ)} := by
  apply (convex_signed E L).isPathConnected
  refine ⟨signedPoint E L,?_⟩
  change (toHeads (signedPoint E L)).IsSigned (L : α → ℝ)
  rw [toHeads_signedPoint]
  exact signedHeads_isSigned _

/-- A split coefficient family is path connected when its decomposition is attained. -/
theorem isPathConnected_split (E : Submodule ℝ (α → ℝ)) (L A B : E)
    (hA : ∀ x, 0 ≤ (A : α → ℝ) x) (hB : ∀ x, 0 ≤ (B : α → ℝ) x)
    (hL : A-B=L) :
    IsPathConnected {p : Data E | (toHeads p).IsSplit (L : α → ℝ)} :=
  (convex_split E L).isPathConnected ⟨splitPoint E A B,splitPoint_isSplit E L A B hA hB hL⟩

/-- Shrink the cross coefficients in the physical parameter space. -/
noncomputable def shrinkPoint {E : Submodule ℝ (α → ℝ)} (p : Data E) (s : ℝ) : Data E :=
  (![1+s*(p.1 0-1),s*p.1 1,s*p.1 2,1+s*(p.1 3-1)],p.2.1,p.2.2)

lemma toHeads_shrinkPoint {E : Submodule ℝ (α → ℝ)} (p : Data E) (s : ℝ) :
    toHeads (shrinkPoint p s)=shrink s (toHeads p) := rfl

lemma continuous_shrinkPoint {E : Submodule ℝ (α → ℝ)} (p : Data E) :
    Continuous (shrinkPoint p) := by
  apply Continuous.prod_mk
  · apply continuous_pi
    intro i
    fin_cases i <;> norm_num [shrinkPoint] <;> continuity
  · exact continuous_const

lemma shrinkPoint_one {E : Submodule ℝ (α → ℝ)} (p : Data E) : shrinkPoint p 1=p := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [shrinkPoint] <;> rfl
  · rfl

lemma shrinkPoint_zero_split {E : Submodule ℝ (α → ℝ)} (p : Data E)
    {L : α → ℝ} (hp : (toHeads p).IsSplitHybrid L) :
    (toHeads (shrinkPoint p 0)).IsSplit L := by
  rw [toHeads_shrinkPoint]
  exact shrink_zero_isSplit hp

lemma shrinkPoint_joined {E : Submodule ℝ (α → ℝ)} (p : Data E)
    {L : α → ℝ} (hp : (toHeads p).IsSplitHybrid L) :
    JoinedIn {q : Data E | (toHeads q).IsSplitHybrid L} (shrinkPoint p 0) p := by
  refine JoinedIn.ofLine (continuous_shrinkPoint p).continuousOn rfl
    (shrinkPoint_one p) ?_
  rintro q ⟨s,hs,rfl⟩
  rw [Set.mem_setOf_eq,toHeads_shrinkPoint]
  exact shrink_splitHybrid hp hs.1

/-- The hybrid attachments introduce no additional component. This is a path in
actual scalar coefficients and intercept functions, not merely an output recoding. -/
theorem isPathConnected_splitHybrid (E : Submodule ℝ (α → ℝ)) (L A B : E)
    (hA : ∀ x, 0 ≤ (A : α → ℝ) x) (hB : ∀ x, 0 ≤ (B : α → ℝ) x)
    (hL : A-B=L) :
    IsPathConnected {p : Data E | (toHeads p).IsSplitHybrid (L : α → ℝ)} := by
  let p0 := splitPoint E A B
  have hp0 : (toHeads p0).IsSplit (L : α → ℝ) := splitPoint_isSplit E L A B hA hB hL
  refine ⟨p0,Or.inl hp0,?_⟩
  intro p hp
  have hz : (toHeads (shrinkPoint p 0)).IsSplit (L : α → ℝ) :=
    shrinkPoint_zero_split p hp
  have hpath := (isPathConnected_split E L A B hA hB hL).joinedIn p0 hp0
    (shrinkPoint p 0) hz
  exact (hpath.mono fun _ h => Or.inl h).trans (shrinkPoint_joined p hp)

/-- All real coefficient pairs reconstructing one fixed invariant remainder. -/
abbrev Fiber (E : Submodule ℝ (α → ℝ)) (L : E) :=
  {p : Data E // (toHeads p).Reconstructs (L : α → ℝ)}

def signedSector (E : Submodule ℝ (α → ℝ)) (L : E) : Set (Fiber E L) :=
  {p | (toHeads p.val).IsSigned (L : α → ℝ)}

lemma fiber_exhaustive [Nonempty α] (E : Submodule ℝ (α → ℝ)) (hE : ClippingRigid E)
    (L : E) (p : Fiber E L) :
    (toHeads p.val).IsSigned (L : α → ℝ) ∨
      (toHeads p.val).IsSplitHybrid (L : α → ℝ) :=
  (Heads.reconstructs_iff_signed_or_splitHybrid E hE (toHeads p.val) L
    p.val.2.1.property p.val.2.2.property L.property).mp p.property

lemma signedSector_isClopen_of_pos [Nonempty α] (E : Submodule ℝ (α → ℝ))
    (hE : ClippingRigid E) (L : E) (hL : ∃ x, 0 < (L : α → ℝ) x) :
    IsClopen (signedSector E L) := by
  have hc : Continuous (fun p : Fiber E L => p.val.1 1) :=
    ((continuous_apply 1).comp continuous_fst).comp continuous_subtype_val
  have hopen : signedSector E L={p : Fiber E L | p.val.1 1 < -(1/2 : ℝ)} := by
    ext p
    exact Heads.signed_iff_b_lt_neg_half E hE (toHeads p.val) L
      p.val.2.1.property p.val.2.2.property L.property p.property hL
  have hclosed : signedSector E L={p : Fiber E L | p.val.1 1 = -1} := by
    ext p
    constructor
    · intro hp
      exact hp.2.2.2.2.2.2.1 hL
    · intro hp
      rw [hopen]
      change p.val.1 1 < -(1/2 : ℝ)
      rw [hp]
      norm_num
  constructor
  · rw [hopen]
    exact isOpen_lt hc continuous_const
  · rw [hclosed]
    exact isClosed_eq hc continuous_const

lemma signedSector_isClopen_of_neg [Nonempty α] (E : Submodule ℝ (α → ℝ))
    (hE : ClippingRigid E) (L : E) (hL : ∃ x, (L : α → ℝ) x < 0) :
    IsClopen (signedSector E L) := by
  have hc : Continuous (fun p : Fiber E L => p.val.1 2) :=
    ((continuous_apply 2).comp continuous_fst).comp continuous_subtype_val
  have hopen : signedSector E L={p : Fiber E L | p.val.1 2 < -(1/2 : ℝ)} := by
    ext p
    exact Heads.signed_iff_c_lt_neg_half E hE (toHeads p.val) L
      p.val.2.1.property p.val.2.2.property L.property p.property hL
  have hclosed : signedSector E L={p : Fiber E L | p.val.1 2 = -1} := by
    ext p
    constructor
    · intro hp
      exact hp.2.2.2.2.2.2.2 hL
    · intro hp
      rw [hopen]
      change p.val.1 2 < -(1/2 : ℝ)
      rw [hp]
      norm_num
  constructor
  · rw [hopen]
    exact isOpen_lt hc continuous_const
  · rw [hclosed]
    exact isClosed_eq hc continuous_const

/-- The two reconstruction types are separated by a genuine clopen condition
in the complete exact reconstruction fiber. -/
theorem signedSector_isClopen (E : Submodule ℝ (α → ℝ)) (hE : ClippingRigid E)
    (L : E) (hL : ∃ x, (L : α → ℝ) x ≠ 0) : IsClopen (signedSector E L) := by
  obtain ⟨x,hx⟩ := hL
  letI : Nonempty α := ⟨x⟩
  rcases lt_or_gt_of_ne hx with hx | hx
  · exact signedSector_isClopen_of_neg E hE L ⟨x,hx⟩
  · exact signedSector_isClopen_of_pos E hE L ⟨x,hx⟩

theorem isPathConnected_signedSector (E : Submodule ℝ (α → ℝ)) (L : E) :
    IsPathConnected (signedSector E L) := by
  have hind : Inducing (Subtype.val : Fiber E L → Data E) := inducing_subtype_val
  apply hind.isPathConnected_iff.mpr
  have he : (Subtype.val : Fiber E L → Data E) '' signedSector E L =
      {p : Data E | (toHeads p).IsSigned (L : α → ℝ)} := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact hq
    · intro hp
      exact ⟨⟨p,hp.reconstructs⟩,hp,rfl⟩
  exact he.symm ▸ isPathConnected_signed E L

theorem isPathConnected_compl_signedSector (E : Submodule ℝ (α → ℝ))
    (hE : ClippingRigid E) (L A B : E)
    (hA : ∀ x, 0 ≤ (A : α → ℝ) x) (hB : ∀ x, 0 ≤ (B : α → ℝ) x)
    (hL : A-B=L) (hL0 : ∃ x, (L : α → ℝ) x ≠ 0) :
    IsPathConnected (signedSector E L)ᶜ := by
  letI : Nonempty α := ⟨hL0.choose⟩
  have hind : Inducing (Subtype.val : Fiber E L → Data E) := inducing_subtype_val
  apply hind.isPathConnected_iff.mpr
  have he : (Subtype.val : Fiber E L → Data E) '' (signedSector E L)ᶜ =
      {p : Data E | (toHeads p).IsSplitHybrid (L : α → ℝ)} := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact (fiber_exhaustive E hE L q).resolve_left hq
    · intro hp
      refine ⟨⟨p,hp.reconstructs⟩,?_,rfl⟩
      intro hs
      exact Heads.signed_not_splitHybrid hL0 hs hp
  exact he.symm ▸ isPathConnected_splitHybrid E L A B hA hB hL

/-- The exact two-head reconstruction fiber has two connected components.
The hypotheses are properties of the actual invariant function space and an
attained nonnegative decomposition; no connectedness conclusion is assumed. -/
noncomputable def headComponentsEquivBool (E : Submodule ℝ (α → ℝ))
    (hE : ClippingRigid E) (L A B : E)
    (hA : ∀ x, 0 ≤ (A : α → ℝ) x) (hB : ∀ x, 0 ≤ (B : α → ℝ) x)
    (hL : A-B=L) (hL0 : ∃ x, (L : α → ℝ) x ≠ 0) :
    ConnectedComponents (Fiber E L) ≃ Bool := by
  let label := (signedSector E L).boolIndicator
  have hcont : Continuous label :=
    (continuous_boolIndicator_iff_isClopen _).mpr (signedSector_isClopen E hE L hL0)
  have hsurj : Surjective label := by
    intro b
    cases b
    · obtain ⟨p,hp,_⟩ := isPathConnected_compl_signedSector E hE L A B hA hB hL hL0
      exact ⟨p,((signedSector E L).not_mem_iff_boolIndicator p).mp hp⟩
    · obtain ⟨p,hp,_⟩ := isPathConnected_signedSector E L
      exact ⟨p,((signedSector E L).mem_iff_boolIndicator p).mp hp⟩
  have hfib : ∀ b, IsPreconnected (label ⁻¹' {b}) := by
    intro b
    cases b
    · change IsPreconnected ((signedSector E L).boolIndicator ⁻¹' {false})
      rw [Set.preimage_boolIndicator_false]
      exact (isPathConnected_compl_signedSector E hE L A B hA hB hL hL0).isConnected.2
    · change IsPreconnected ((signedSector E L).boolIndicator ⁻¹' {true})
      rw [Set.preimage_boolIndicator_true]
      exact (isPathConnected_signedSector E L).isConnected.2
  exact connectedComponentsEquiv hcont hsurj hfib

/-- An explicit finite equivalence, retaining finiteness as well as cardinality. -/
theorem has_two_head_components (E : Submodule ℝ (α → ℝ))
    (hE : ClippingRigid E) (L A B : E)
    (hA : ∀ x, 0 ≤ (A : α → ℝ) x) (hB : ∀ x, 0 ≤ (B : α → ℝ) x)
    (hL : A-B=L) (hL0 : ∃ x, (L : α → ℝ) x ≠ 0) :
    Nonempty (ConnectedComponents (Fiber E L) ≃ Fin 2) := by
  exact ⟨(headComponentsEquivBool E hE L A B hA hB hL hL0).trans
    (Fintype.equivFinOfCardEq (by decide : Fintype.card Bool=2))⟩

/-- Nonnegative invariant features supply the decomposition used by the topology
argument. The coefficients may be arbitrary real numbers. -/
theorem exists_nonnegative_decomposition {κ : Type*} [Fintype κ]
    (E : Submodule ℝ (α → ℝ)) (φ : κ → E)
    (hφ : ∀ i x, 0 ≤ (φ i : α → ℝ) x) (L : E)
    (hL : ∃ c : κ → ℝ, L=∑ i, c i • φ i) :
    ∃ A B : E, (∀ x, 0 ≤ (A : α → ℝ) x) ∧
      (∀ x, 0 ≤ (B : α → ℝ) x) ∧ A-B=L := by
  classical
  obtain ⟨c,hc⟩ := hL
  let A : E := ∑ i, relu (c i) • φ i
  let B : E := ∑ i, relu (-c i) • φ i
  refine ⟨A,B,?_,?_,?_⟩
  · intro x
    change 0 ≤ ((∑ i, relu (c i) • φ i : E) : α → ℝ) x
    simp only [Submodule.coe_sum,Finset.sum_apply,Submodule.coe_smul,Pi.smul_apply,smul_eq_mul]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (relu_nonneg _) (hφ i x)
  · intro x
    change 0 ≤ ((∑ i, relu (-c i) • φ i : E) : α → ℝ) x
    simp only [Submodule.coe_sum,Finset.sum_apply,Submodule.coe_smul,Pi.smul_apply,smul_eq_mul]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (relu_nonneg _) (hφ i x)
  · rw [hc]
    change (∑ i, relu (c i) • φ i)-(∑ i, relu (-c i) • φ i)=∑ i, c i • φ i
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Subtype.ext
    funext x
    change relu (c i)*(φ i : α → ℝ) x-relu (-c i)*(φ i : α → ℝ) x=
      c i*(φ i : α → ℝ) x
    rw [← sub_mul,relu_sub_relu_neg]

/-- A directly usable form for invariant spaces spanned by nonnegative features. -/
theorem has_two_head_components_of_features {κ : Type*} [Fintype κ]
    (E : Submodule ℝ (α → ℝ)) (hE : ClippingRigid E) (φ : κ → E)
    (hφ : ∀ i x, 0 ≤ (φ i : α → ℝ) x) (L : E)
    (hspan : ∃ c : κ → ℝ, L=∑ i, c i • φ i)
    (hL0 : ∃ x, (L : α → ℝ) x ≠ 0) :
    Nonempty (ConnectedComponents (Fiber E L) ≃ Fin 2) := by
  obtain ⟨A,B,hA,hB,hL⟩ := exists_nonnegative_decomposition E φ hφ L hspan
  exact has_two_head_components E hE L A B hA hB hL hL0

section Bundles
variable {β : Type*} [TopologicalSpace β]

private lemma joinedIn_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {S : Set X} {T : Set Y} {x y : X} (h : JoinedIn S x y)
    (f : X → Y) (hf : Continuous f) (hmap : MapsTo f S T) :
    JoinedIn T (f x) (f y) :=
  ⟨h.somePath.map hf,fun t => hmap (h.somePath_mem t)⟩

/-- A continuous canonical section and actual paths to it suffice for total-space
path connectedness. There is no assertion that arbitrary base paths lift. -/
private lemma isPathConnected_of_section {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {S : Set X} {T : Set Y}
    (f : Y → X) (hf : Continuous f) (hmap : MapsTo f T S) (hT : IsPathConnected T)
    (hjoin : ∀ x ∈ S, ∃ y ∈ T, JoinedIn S x (f y)) : IsPathConnected S := by
  obtain ⟨b,hb,hbjoin⟩ := hT
  refine ⟨f b,hmap hb,?_⟩
  intro x hx
  obtain ⟨a,ha,hxa⟩ := hjoin x hx
  have hba := joinedIn_map (hbjoin ha) f hf hmap
  exact hba.trans hxa.symm

lemma continuous_signedPoint (E : Submodule ℝ (α → ℝ)) :
    Continuous (signedPoint E) :=
  continuous_const.prod_mk (continuous_id.prod_mk continuous_neg)

/-- The signed reconstruction type stays path connected over a path-connected
residual parameter domain. This justifies varying residuals, rather than
multiplying counts of one projection and one typical fiber. -/
theorem isPathConnected_signed_bundle (E : Submodule ℝ (α → ℝ))
    (base : Set β) (L : β → E) (hbase : IsPathConnected base) (hL : Continuous L) :
    IsPathConnected {p : β × Data E | p.1 ∈ base ∧
      (toHeads p.2).IsSigned (L p.1 : α → ℝ)} := by
  let s : β → β × Data E := fun b => (b,signedPoint E (L b))
  have hs : Continuous s := continuous_id.prod_mk ((continuous_signedPoint E).comp hL)
  refine isPathConnected_of_section s hs ?_ hbase ?_
  · intro b hb
    refine ⟨hb,?_⟩
    rw [toHeads_signedPoint]
    exact signedHeads_isSigned _
  · intro p hp
    refine ⟨p.1,hp.1,?_⟩
    have hc : (toHeads (signedPoint E (L p.1))).IsSigned (L p.1 : α → ℝ) := by
      rw [toHeads_signedPoint]
      exact signedHeads_isSigned _
    have hpath := (isPathConnected_signed E (L p.1)).joinedIn p.2 hp.2
      (signedPoint E (L p.1)) hc
    exact joinedIn_map hpath (fun q => (p.1,q))
      (continuous_const.prod_mk continuous_id) (fun _ h => ⟨hp.1,h⟩)

lemma continuous_splitPoint (E : Submodule ℝ (α → ℝ)) (A B : β → E)
    (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun b => splitPoint E (A b) (B b)) :=
  continuous_const.prod_mk (hA.prod_mk hB)

/-- The split/hybrid type also stays connected as residual parameters vary,
provided one continuous nonnegative decomposition is chosen. -/
theorem isPathConnected_splitHybrid_bundle (E : Submodule ℝ (α → ℝ))
    (base : Set β) (L A B : β → E) (hbase : IsPathConnected base)
    (hcA : Continuous A) (hcB : Continuous B)
    (hA : ∀ b ∈ base, ∀ x, 0 ≤ (A b : α → ℝ) x)
    (hB : ∀ b ∈ base, ∀ x, 0 ≤ (B b : α → ℝ) x)
    (hL : ∀ b ∈ base, A b-B b=L b) :
    IsPathConnected {p : β × Data E | p.1 ∈ base ∧
      (toHeads p.2).IsSplitHybrid (L p.1 : α → ℝ)} := by
  let s : β → β × Data E := fun b => (b,splitPoint E (A b) (B b))
  have hs : Continuous s := continuous_id.prod_mk (continuous_splitPoint E A B hcA hcB)
  refine isPathConnected_of_section s hs ?_ hbase ?_
  · intro b hb
    exact ⟨hb,Or.inl (splitPoint_isSplit E (L b) (A b) (B b) (hA b hb) (hB b hb) (hL b hb))⟩
  · intro p hp
    refine ⟨p.1,hp.1,?_⟩
    have hc : (toHeads (splitPoint E (A p.1) (B p.1))).IsSplitHybrid
        (L p.1 : α → ℝ) :=
      Or.inl (splitPoint_isSplit E (L p.1) (A p.1) (B p.1)
        (hA p.1 hp.1) (hB p.1 hp.1) (hL p.1 hp.1))
    have hpath := (isPathConnected_splitHybrid E (L p.1) (A p.1) (B p.1)
      (hA p.1 hp.1) (hB p.1 hp.1) (hL p.1 hp.1)).joinedIn p.2 hp.2
        (splitPoint E (A p.1) (B p.1)) hc
    exact joinedIn_map hpath (fun q => (p.1,q))
      (continuous_const.prod_mk continuous_id) (fun _ h => ⟨hp.1,h⟩)
end Bundles

/-- Uniform reconstruction-type test requiring no choice of a positive or
negative witness for the nonzero remainder. -/
lemma signed_iff_intercepts (E : Submodule ℝ (α → ℝ)) (hE : ClippingRigid E)
    (h : Heads α) (L : α → ℝ) (hA : h.A ∈ E) (hB : h.B ∈ E) (hL : L ∈ E)
    (hr : h.Reconstructs L) (hnz : ∃ x, L x ≠ 0) :
    h.IsSigned L ↔ h.A=L ∧ h.B=(fun x => -L x) := by
  letI : Nonempty α := ⟨hnz.choose⟩
  constructor
  · intro hs
    exact ⟨hs.1,hs.2.1⟩
  · intro hab
    rcases (Heads.reconstructs_iff_signed_or_splitHybrid E hE h L hA hB hL).mp hr with hs | ht
    · exact hs
    · obtain ⟨x,hx⟩ := hnz
      obtain ⟨hp,hq⟩ := ht.intercepts_nonneg
      have hp' : 0 ≤ L x := by simpa only [hab.1] using hp x
      have hq' : 0 ≤ -L x := by simpa only [hab.2] using hq x
      exact (hx (by linarith)).elim

lemma splitHybrid_iff_nonnegative_intercepts (E : Submodule ℝ (α → ℝ))
    (hE : ClippingRigid E) (h : Heads α) (L : α → ℝ)
    (hA : h.A ∈ E) (hB : h.B ∈ E) (hL : L ∈ E)
    (hr : h.Reconstructs L) (hnz : ∃ x, L x ≠ 0) :
    h.IsSplitHybrid L ↔ (∀ x, 0 ≤ h.A x) ∧ (∀ x, 0 ≤ h.B x) := by
  letI : Nonempty α := ⟨hnz.choose⟩
  constructor
  · exact Heads.IsSplitHybrid.intercepts_nonneg
  · intro hab
    rcases (Heads.reconstructs_iff_signed_or_splitHybrid E hE h L hA hB hL).mp hr with hs | ht
    · obtain ⟨x,hx⟩ := hnz
      have hp : 0 ≤ L x := by simpa only [hs.1] using hab.1 x
      have hq : 0 ≤ -L x := by simpa only [hs.2.1] using hab.2 x
      exact (hx (by linarith)).elim
    · exact ht

section VaryingRemainder
variable {β : Type*} [TopologicalSpace β]

/-- The complete physical two-head family with a varying invariant remainder. -/
abbrev BundleFiber (E : Submodule ℝ (α → ℝ)) (L : β → E) :=
  {p : β × Data E // (toHeads p.2).Reconstructs (L p.1 : α → ℝ)}

def bundleSignedSector (E : Submodule ℝ (α → ℝ)) (L : β → E) :
    Set (BundleFiber E L) := {p | (toHeads p.val.2).IsSigned (L p.val.1 : α → ℝ)}

/-- Both reconstruction types are closed as the nonzero remainder varies.
Together with exhaustion this proves the signed type is clopen. -/
theorem bundleSignedSector_isClopen (E : Submodule ℝ (α → ℝ))
    (hE : ClippingRigid E) (L : β → E) (hcL : Continuous L)
    (hnz : ∀ b, ∃ x, (L b : α → ℝ) x ≠ 0) :
    IsClopen (bundleSignedSector E L) := by
  have hcA (x : α) : Continuous (fun p : BundleFiber E L => (p.val.2.2.1 : α → ℝ) x) :=
    ((continuous_apply x).comp continuous_subtype_val).comp
      (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)))
  have hcB (x : α) : Continuous (fun p : BundleFiber E L => (p.val.2.2.2 : α → ℝ) x) :=
    ((continuous_apply x).comp continuous_subtype_val).comp
      (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)))
  have hcR (x : α) : Continuous (fun p : BundleFiber E L => (L p.val.1 : α → ℝ) x) :=
    ((continuous_apply x).comp continuous_subtype_val).comp
      (hcL.comp (continuous_fst.comp continuous_subtype_val))
  have hclosed : IsClosed (bundleSignedSector E L) := by
    have he : bundleSignedSector E L =
        ⋂ x : α, {p : BundleFiber E L |
          (p.val.2.2.1 : α → ℝ) x=(L p.val.1 : α → ℝ) x ∧
          (p.val.2.2.2 : α → ℝ) x = -(L p.val.1 : α → ℝ) x} := by
      ext p
      rw [Set.mem_iInter]
      change (toHeads p.val.2).IsSigned (L p.val.1 : α → ℝ) ↔ _
      rw [signed_iff_intercepts E hE (toHeads p.val.2) (L p.val.1)
        p.val.2.2.1.property p.val.2.2.2.property (L p.val.1).property p.property (hnz p.val.1)]
      constructor
      · rintro ⟨ha,hb⟩ x
        exact ⟨congrFun ha x,congrFun hb x⟩
      · intro h
        exact ⟨funext fun x => (h x).1,funext fun x => (h x).2⟩
    rw [he]
    apply isClosed_iInter
    intro x
    exact (isClosed_eq (hcA x) (hcR x)).inter (isClosed_eq (hcB x) (hcR x).neg)
  have hcompl : IsClosed (bundleSignedSector E L)ᶜ := by
    have he : (bundleSignedSector E L)ᶜ =
        ⋂ x : α, {p : BundleFiber E L | 0 ≤ (p.val.2.2.1 : α → ℝ) x ∧
          0 ≤ (p.val.2.2.2 : α → ℝ) x} := by
      ext p
      rw [Set.mem_iInter]
      change ¬ (toHeads p.val.2).IsSigned (L p.val.1 : α → ℝ) ↔ _
      have hx := hnz p.val.1
      letI : Nonempty α := ⟨hx.choose⟩
      have he := (Heads.reconstructs_iff_signed_or_splitHybrid E hE
        (toHeads p.val.2) (L p.val.1) p.val.2.2.1.property p.val.2.2.2.property
        (L p.val.1).property).mp p.property
      constructor
      · intro hp
        obtain ⟨ha,hb⟩ := (he.resolve_left hp).intercepts_nonneg
        exact fun x => ⟨ha x,hb x⟩
      · intro hp hs
        obtain ⟨x,hx⟩ := hx
        have ha : 0 ≤ (L p.val.1 : α → ℝ) x := by
          have hh := (hp x).1
          change 0 ≤ (toHeads p.val.2).A x at hh
          rw [hs.1] at hh
          exact hh
        have hb : 0 ≤ -(L p.val.1 : α → ℝ) x := by
          have hh := (hp x).2
          change 0 ≤ (toHeads p.val.2).B x at hh
          rw [hs.2.1] at hh
          exact hh
        exact hx (by linarith)
    rw [he]
    apply isClosed_iInter
    intro x
    exact (isClosed_le continuous_const (hcA x)).inter (isClosed_le continuous_const (hcB x))
  exact ⟨by simpa only [compl_compl] using hcompl.isOpen_compl,hclosed⟩
/-- The signed total family is path connected, in the whole reconstruction fiber. -/
theorem bundleSignedSector_isPathConnected [PathConnectedSpace β]
    (E : Submodule ℝ (α → ℝ)) (L : β → E) (hcL : Continuous L) :
    IsPathConnected (bundleSignedSector E L) := by
  have hind : Inducing (Subtype.val : BundleFiber E L → β × Data E) := inducing_subtype_val
  apply hind.isPathConnected_iff.mpr
  have he : (Subtype.val : BundleFiber E L → β × Data E) '' bundleSignedSector E L =
      {p : β × Data E | (toHeads p.2).IsSigned (L p.1 : α → ℝ)} := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact hq
    · intro hp
      exact ⟨⟨p,hp.reconstructs⟩,hp,rfl⟩
  have hp : IsPathConnected {p : β × Data E | (toHeads p.2).IsSigned (L p.1 : α → ℝ)} := by
    simpa only [Set.mem_univ,true_and] using
      isPathConnected_signed_bundle E Set.univ L isPathConnected_univ hcL
  exact he.symm ▸ hp

/-- The hybrid total family remains path connected through global-sign changes
of the invariant remainder. -/
theorem bundleComplement_isPathConnected [PathConnectedSpace β]
    (E : Submodule ℝ (α → ℝ)) (hE : ClippingRigid E) (L A B : β → E)
    (hcA : Continuous A) (hcB : Continuous B)
    (hA : ∀ b x, 0 ≤ (A b : α → ℝ) x) (hB : ∀ b x, 0 ≤ (B b : α → ℝ) x)
    (hL : ∀ b, A b-B b=L b) (hnz : ∀ b, ∃ x, (L b : α → ℝ) x ≠ 0) :
    IsPathConnected (bundleSignedSector E L)ᶜ := by
  have hind : Inducing (Subtype.val : BundleFiber E L → β × Data E) := inducing_subtype_val
  apply hind.isPathConnected_iff.mpr
  have he : (Subtype.val : BundleFiber E L → β × Data E) '' (bundleSignedSector E L)ᶜ =
      {p : β × Data E | (toHeads p.2).IsSplitHybrid (L p.1 : α → ℝ)} := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩
      letI : Nonempty α := ⟨(hnz q.val.1).choose⟩
      exact ((Heads.reconstructs_iff_signed_or_splitHybrid E hE (toHeads q.val.2)
        (L q.val.1) q.val.2.2.1.property q.val.2.2.2.property (L q.val.1).property).mp
        q.property).resolve_left hq
    · intro hp
      refine ⟨⟨p,hp.reconstructs⟩,?_,rfl⟩
      intro hs
      exact Heads.signed_not_splitHybrid (hnz p.1) hs hp
  have hp : IsPathConnected {p : β × Data E | (toHeads p.2).IsSplitHybrid (L p.1 : α → ℝ)} := by
    simpa only [Set.mem_univ,true_and] using
      isPathConnected_splitHybrid_bundle E Set.univ L A B isPathConnected_univ
        hcA hcB (fun b _ => hA b) (fun b _ => hB b) (fun b _ => hL b)
  exact he.symm ▸ hp

/-- Exactly two head components over an entire connected residual parameter
family. In particular, this is stronger than a count in one typical fiber. -/
noncomputable def bundleComponentsEquivBool [PathConnectedSpace β]
    (E : Submodule ℝ (α → ℝ)) (hE : ClippingRigid E) (L A B : β → E)
    (hcA : Continuous A) (hcB : Continuous B)
    (hA : ∀ b x, 0 ≤ (A b : α → ℝ) x) (hB : ∀ b x, 0 ≤ (B b : α → ℝ) x)
    (hL : ∀ b, A b-B b=L b) (hnz : ∀ b, ∃ x, (L b : α → ℝ) x ≠ 0) :
    ConnectedComponents (BundleFiber E L) ≃ Bool := by
  have hcL : Continuous L := (hcA.sub hcB).congr (fun b => hL b)
  let S := bundleSignedSector E L
  let label := S.boolIndicator
  have hcont : Continuous label :=
    (continuous_boolIndicator_iff_isClopen _).mpr (bundleSignedSector_isClopen E hE L hcL hnz)
  have hs := bundleSignedSector_isPathConnected E L hcL
  have hc := bundleComplement_isPathConnected E hE L A B hcA hcB hA hB hL hnz
  have hsurj : Surjective label := by
    intro b
    cases b
    · obtain ⟨p,hp,_⟩ := hc
      exact ⟨p,(S.not_mem_iff_boolIndicator p).mp hp⟩
    · obtain ⟨p,hp,_⟩ := hs
      exact ⟨p,(S.mem_iff_boolIndicator p).mp hp⟩
  have hfib : ∀ b, IsPreconnected (label ⁻¹' {b}) := by
    intro b
    cases b
    · change IsPreconnected (S.boolIndicator ⁻¹' {false})
      rw [Set.preimage_boolIndicator_false]
      exact hc.isConnected.2
    · change IsPreconnected (S.boolIndicator ⁻¹' {true})
      rw [Set.preimage_boolIndicator_true]
      exact hs.isConnected.2
  exact connectedComponentsEquiv hcont hsurj hfib

theorem has_two_head_bundle_components [PathConnectedSpace β]
    (E : Submodule ℝ (α → ℝ)) (hE : ClippingRigid E) (L A B : β → E)
    (hcA : Continuous A) (hcB : Continuous B)
    (hA : ∀ b x, 0 ≤ (A b : α → ℝ) x) (hB : ∀ b x, 0 ≤ (B b : α → ℝ) x)
    (hL : ∀ b, A b-B b=L b) (hnz : ∀ b, ∃ x, (L b : α → ℝ) x ≠ 0) :
    Nonempty (ConnectedComponents (BundleFiber E L) ≃ Fin 2) :=
  ⟨(bundleComponentsEquivBool E hE L A B hcA hcB hA hB hL hnz).trans
    (Fintype.equivFinOfCardEq (by decide : Fintype.card Bool=2))⟩

end VaryingRemainder


#check @has_two_head_components
#print axioms isPathConnected_signed
#print axioms isPathConnected_splitHybrid
#print axioms signedSector_isClopen
#print axioms has_two_head_components
#print axioms has_two_head_components_of_features
#print axioms isPathConnected_signed_bundle
#print axioms isPathConnected_splitHybrid_bundle
#print axioms bundleSignedSector_isClopen
#print axioms bundleComponentsEquivBool
#print axioms has_two_head_bundle_components
end MaxCaterpillar.Fiber.Count65.HeadTopology
