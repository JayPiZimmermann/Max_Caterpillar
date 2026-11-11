import MaxCaterpillar.Fiber.Count65.Topology

/-! # Continuous labels from a finite actual closed partition -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.FiniteClosedPartition
open Set
variable {X L : Type*} [TopologicalSpace X] [Finite L]

noncomputable def classify (S : L → Set X) (cover : ∀ x, ∃ l, x ∈ S l) (x : X) : L :=
  Classical.choose (cover x)

lemma classify_mem (S : L → Set X) (cover : ∀ x, ∃ l, x ∈ S l) (x : X) :
    x ∈ S (classify S cover x) := Classical.choose_spec (cover x)

lemma classify_eq_iff (S : L → Set X) (cover : ∀ x, ∃ l, x ∈ S l)
    (unique : ∀ x l m, x ∈ S l → x ∈ S m → l=m) (x : X) (l : L) :
    classify S cover x=l ↔ x ∈ S l := by
  constructor
  · intro h
    rw [← h]
    exact classify_mem S cover x
  · exact fun h => unique x _ _ (classify_mem S cover x) h

lemma isClopen_class (S : L → Set X) (closed : ∀ l, IsClosed (S l))
    (cover : ∀ x, ∃ l, x ∈ S l)
    (unique : ∀ x l m, x ∈ S l → x ∈ S m → l=m) (l : L) : IsClopen (S l) := by
  have he : (S l)ᶜ = ⋃ m : {m : L // m ≠ l}, S m.val := by
    ext x
    constructor
    · intro hx
      obtain ⟨m,hm⟩ := cover x
      have hne : m ≠ l := by intro h; exact hx (h ▸ hm)
      exact Set.mem_iUnion.mpr ⟨⟨m,hne⟩,hm⟩
    · intro hx hl
      obtain ⟨m,hm⟩ := Set.mem_iUnion.mp hx
      exact m.property (unique x _ _ hm hl)
  have hc : IsClosed (S l)ᶜ := by
    rw [he]
    exact isClosed_iUnion_of_finite (fun m => closed m.val)
  exact ⟨by simpa only [compl_compl] using hc.isOpen_compl,closed l⟩

/-- Closedness and the exhaustive unique class cover prove continuity; no
continuity of an existential normal-form choice is assumed. -/
theorem continuous_classify [TopologicalSpace L] (S : L → Set X)
    (closed : ∀ l, IsClosed (S l)) (cover : ∀ x, ∃ l, x ∈ S l)
    (unique : ∀ x l m, x ∈ S l → x ∈ S m → l=m) :
    Continuous (classify S cover) := by
  apply continuous_def.2
  intro u _
  have he : classify S cover ⁻¹' u = ⋃ l : {l : L // l ∈ u}, S l.val := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨⟨classify S cover x,hx⟩,classify_mem S cover x⟩
    · intro hx
      obtain ⟨l,hl⟩ := Set.mem_iUnion.mp hx
      have h := (classify_eq_iff S cover unique x l.val).mpr hl
      change classify S cover x ∈ u
      rw [h]
      exact l.property
  rw [he]
  exact isOpen_iUnion fun l => (isClopen_class S closed cover unique l.val).isOpen

#print axioms continuous_classify
end MaxCaterpillar.Fiber.Count65.FiniteClosedPartition
