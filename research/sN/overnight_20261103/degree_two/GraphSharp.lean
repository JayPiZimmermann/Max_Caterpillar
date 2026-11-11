import research.sN.overnight_20261103.degree_two.GraphConnected
import research.sN.overnight_20261103.degree_two.GraphCapacity

/-! Two orientations of a spanning simple path sharpen the connected-set
budget from 2N to N, including cycles and disconnected ambient graphs. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.DegreeTwo
open SimpleGraph BigOperators
attribute [local instance] Classical.propDecidable
variable {N : ℕ}

private def DartSupports (G : SimpleGraph (Fin N)) (k : ℕ) (d : G.Dart)
    (S : Finset (Fin N)) : Prop :=
  ∃ b, ∃ p : G.Walk d.fst b,
    p.IsPath ∧ p.length+1=k ∧ p.getVert 1=d.snd ∧ p.support.toFinset=S

private lemma dartSupports_unique (G : SimpleGraph (Fin N))
    (hdegree : ∀ v, G.degree v≤2) (k : ℕ) (d : G.Dart)
    {S T : Finset (Fin N)} (hS : DartSupports G k d S) (hT : DartSupports G k d T) :
    S=T := by
  obtain ⟨b,p,hp,hpk,hpd,hpS⟩ := hS
  obtain ⟨c,q,hq,hqk,hqd,hqT⟩ := hT
  have hlen : p.length=q.length := Nat.add_right_cancel (hpk.trans hqk.symm)
  have hs := ExponentialPush.DegreeTwo.support_eq_of_first_step G hdegree p q hp hq hlen
    (hpd.trans hqd.symm)
  rw [←hpS,←hqT]
  exact congrArg List.toFinset hs

private lemma path_start_ne_end (G : SimpleGraph (Fin N)) {a b : Fin N}
    (p : G.Walk a b) (hp : p.IsPath) (hpos : 0<p.length) : a≠b := by
  intro h
  subst b
  have hnil := (Walk.isPath_iff_eq_nil p).mp hp
  have hz : p.length=0 := by rw [hnil]; rfl
  rw [hz] at hpos
  exact Nat.lt_irrefl 0 hpos

/-- A positive-size connected set with at least two vertices gives two
DISTINCT directed edges supporting exactly that set. -/
private lemma two_supporting_darts (G : SimpleGraph (Fin N))
    (hdegree : ∀ v, G.degree v≤2) (k : ℕ) (hk : 2≤k)
    (S : Finset (Fin N)) (hS : S∈connectedSets G k) :
    ∃ d e : G.Dart, d≠e ∧ DartSupports G k d S ∧ DartSupports G k e S := by
  obtain ⟨d,b,p,hp,hlen,hfirst,hsupport⟩ := spanning_dart_exists G hdegree k hk S hS
  have hpos : 0<p.length := by
    have h : 1 < p.length+1 := by rw [hlen]; exact Nat.lt_of_lt_of_le (by decide) hk
    exact Nat.lt_of_succ_lt_succ h
  have hposrev : 0<p.reverse.length := by simpa using hpos
  have hadj : G.Adj b (p.reverse.getVert 1) := by
    simpa using p.reverse.adj_getVert_succ hposrev
  let e : G.Dart := ⟨(b,p.reverse.getVert 1),hadj⟩
  refine ⟨d,e,?_,⟨b,p,hp,hlen,hfirst,hsupport⟩,?_⟩
  · intro heq
    have he : d.fst=b := congrArg (fun t : G.Dart => t.fst) heq
    exact path_start_ne_end G p hp hpos he
  · refine ⟨d.fst,p.reverse,hp.reverse,?_,rfl,?_⟩
    · simpa using hlen
    · simpa using hsupport

/-- Counting both orientations gives twice the subset count, even when a
connected subset spans an entire cycle. -/
theorem two_mul_connectedSets_card_le_darts (G : SimpleGraph (Fin N))
    (hdegree : ∀ v, G.degree v≤2) (k : ℕ) (hk : 2≤k) :
    2*(connectedSets G k).card≤Fintype.card G.Dart := by
  classical
  let f : G.Dart→Finset (Fin N) := fun d =>
    if h : ∃ S, DartSupports G k d S then Classical.choose h else ∅
  have hf : ∀ d S, DartSupports G k d S → f d=S := by
    intro d S hS
    have hex : ∃ T, DartSupports G k d T := ⟨S,hS⟩
    simp only [f,dif_pos hex]
    exact dartSupports_unique G hdegree k d (Classical.choose_spec hex) hS
  have htwo := two_mul_card_le_of_two_preimages
    (Finset.univ : Finset G.Dart) (connectedSets G k) f
    (by
      intro S hS
      obtain ⟨d,e,hde,hd,he⟩ := two_supporting_darts G hdegree k hk S hS
      exact ⟨d,Finset.mem_univ d,e,Finset.mem_univ e,hde,hf d S hd,hf e S he⟩)
  simpa using htwo

/-- Sharp uniform connected-set budget: at most N connected k-subsets. -/
theorem connectedSets_card_le_sharp (G : SimpleGraph (Fin N))
    (hdegree : ∀ v, G.degree v≤2) (k : ℕ) (hk : 0<k) :
    (connectedSets G k).card≤N := by
  classical
  by_cases hk1 : k=1
  · have hsub : connectedSets G k ⊆ Finset.univ.image (fun v : Fin N => ({v} : Finset (Fin N))) := by
      intro S hS
      have hc := ((mem_connectedSets G k S).mp hS).1
      rw [hk1] at hc
      obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hc
      exact Finset.mem_image.mpr ⟨v,Finset.mem_univ v,rfl⟩
    calc
      (connectedSets G k).card ≤ (Finset.univ.image (fun v : Fin N => ({v} : Finset (Fin N)))).card :=
        Finset.card_le_of_subset hsub
      _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_image_le
      _ = N := by simp
  · have hk2 : 2≤k := by
      by_contra hh
      have hle : k≤1 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hh)
      exact hk1 (Nat.le_antisymm hle hk)
    have htwo := two_mul_connectedSets_card_le_darts G hdegree k hk2
    have hd : Fintype.card G.Dart≤2*N := by
      calc
        Fintype.card G.Dart = ∑ v, G.degree v := G.dart_card_eq_sum_degrees
        _ ≤ ∑ _v : Fin N, 2 := Finset.sum_le_sum (fun v _ => hdegree v)
        _ = 2*N := by simp [Nat.mul_comm]
    exact Nat.le_of_mul_le_mul_left (htwo.trans hd) (by decide)

/-- The sharpened actual two-component count, without dividing naturals. -/
theorem two_mul_twoComponentSets_card_le_sharp (G : SimpleGraph (Fin N))
    (hdegree : ∀ v, G.degree v≤2) (m : ℕ) (hm : 0<m) :
    2*(twoComponentSets G m).card≤2*N+(m-1)*N^2 := by
  classical
  let C := connectedSets G
  let E := twoComponentSets G m
  let D := E.filter fun S => S∉C m
  have hD : 2*D.card≤(m-1)*N^2 := by
    apply two_pieces_card_bound C D m N
      (fun k hk => connectedSets_card_le_sharp G hdegree k hk)
    intro S hS
    obtain ⟨hSE,hSC⟩ := Finset.mem_filter.mp hS
    exact (twoComponentSets_decomposition G m hm S hSE).resolve_left hSC
  have hsub : E⊆C m∪D := by
    intro S hS
    by_cases hSC : S∈C m
    · exact Finset.mem_union.mpr (Or.inl hSC)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hS,hSC⟩))
  have hcard := (Finset.card_le_of_subset hsub).trans (Finset.card_union_le (C m) D)
  have hCm := connectedSets_card_le_sharp G hdegree m hm
  change 2*E.card≤2*N+(m-1)*N^2
  change (C m).card≤N at hCm
  calc
    2*E.card ≤ 2*((C m).card+D.card) := Nat.mul_le_mul_left 2 hcard
    _ = 2*(C m).card+2*D.card := Nat.mul_add _ _ _
    _ ≤ 2*N+(m-1)*N^2 := Nat.add_le_add (Nat.mul_le_mul_left 2 hCm) hD

#check @connectedSets_card_le_sharp
#check @two_mul_twoComponentSets_card_le_sharp
#print axioms connectedSets_card_le_sharp
#print axioms two_mul_twoComponentSets_card_le_sharp
end MaxCaterpillar.Overnight.DegreeTwo
