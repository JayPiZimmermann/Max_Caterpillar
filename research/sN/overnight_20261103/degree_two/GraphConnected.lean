import research.sN.overnight_20261103.degree_two.GraphDefs
import research.sN.exponential_push_20261102.degree_two.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! A connected fixed-size set in a graph of maximum degree two has a
spanning simple path. Except for singletons, its chosen first directed edge
determines that path and hence the whole set. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.DegreeTwo
open SimpleGraph BigOperators
attribute [local instance] Classical.propDecidable
variable {N : ℕ}

lemma getVert_copy (G : SimpleGraph (Fin N)) {u v u' v' : Fin N}
    (p : G.Walk u v) (hu : u=u') (hv : v=v') (i : ℕ) :
    (p.copy hu hv).getVert i=p.getVert i := by
  subst_vars
  rfl

theorem connected_set_spanning_path (G : SimpleGraph (Fin N))
    (hdegree : ∀ v, G.degree v ≤ 2) (S : Finset (Fin N))
    (hS : (G.induce (S : Set (Fin N))).Connected) :
    ∃ a b, ∃ p : G.Walk a b, p.IsPath ∧ p.support.toFinset = S := by
  classical
  let H := G.induce (S : Set (Fin N))
  have huniq : ∀ v z a b : {v : Fin N // v ∈ S},
      H.Adj v z → H.Adj v a → H.Adj v b → a ≠ z → b ≠ z → a = b := by
    intro v z a b hvz hva hvb haz hbz
    apply Subtype.ext
    exact ExponentialPush.DegreeTwo.neighbor_eq_of_degree_le_two G (hdegree v.val)
      hvz hva hvb (fun h => haz (Subtype.ext h)) (fun h => hbz (Subtype.ext h))
  obtain ⟨a,b,p,hp,hfull⟩ :=
    ExponentialPush.DegreeTwo.exists_hamiltonian_path_of_unique H hS huniq
  let f : H →g G := { toFun := Subtype.val, map_rel' := fun h => h }
  refine ⟨a.val,b.val,p.map f,Walk.map_isPath_of_injective Subtype.val_injective hp,?_⟩
  ext v
  simp only [List.mem_toFinset,Walk.support_map,List.mem_map]
  constructor
  · rintro ⟨w,_,hw⟩
    exact hw ▸ w.property
  · intro hv
    refine ⟨⟨v,hv⟩,?_,rfl⟩
    have hm : (⟨v,hv⟩ : {v : Fin N // v ∈ S}) ∈ p.support.toFinset := by
      rw [hfull]
      exact Finset.mem_univ _
    exact List.mem_toFinset.mp hm

theorem spanning_dart_exists (G : SimpleGraph (Fin N))
    (hdegree : ∀ v, G.degree v ≤ 2) (k : ℕ) (hk : 2 ≤ k)
    (S : Finset (Fin N)) (hS : S ∈ connectedSets G k) :
    ∃ d : G.Dart, ∃ b, ∃ p : G.Walk d.fst b,
      p.IsPath ∧ p.length+1=k ∧ p.getVert 1=d.snd ∧ p.support.toFinset=S := by
  obtain ⟨hcard,hconn⟩ := (mem_connectedSets G k S).mp hS
  obtain ⟨a,b,p,hp,hsupport⟩ := connected_set_spanning_path G hdegree S hconn
  have hlen : p.length+1=k := by
    rw [←Walk.length_support,←List.toFinset_card_of_nodup hp.support_nodup,hsupport,hcard]
  have hpos : 0<p.length := by omega
  have hadj : G.Adj a (p.getVert 1) := by
    simpa using p.adj_getVert_succ hpos
  exact ⟨⟨(a,p.getVert 1),hadj⟩,b,p,hp,hlen,rfl,hsupport⟩

theorem connectedSets_card_le_darts (G : SimpleGraph (Fin N))
    (hdegree : ∀ v, G.degree v ≤ 2) (k : ℕ) (hk : 2 ≤ k) :
    (connectedSets G k).card ≤ Fintype.card G.Dart := by
  classical
  let C := {S : Finset (Fin N) // S ∈ connectedSets G k}
  have hex : ∀ S : C, ∃ d : G.Dart, ∃ b, ∃ p : G.Walk d.fst b,
      p.IsPath ∧ p.length+1=k ∧ p.getVert 1=d.snd ∧ p.support.toFinset=S.val :=
    fun S => spanning_dart_exists G hdegree k hk S.val S.property
  choose code finish path hpath hlen hfirst hsupport using hex
  have hinj : Function.Injective code := by
    intro S T heq
    have hfst : (code S).fst=(code T).fst := congrArg (fun d : G.Dart => d.fst) heq
    have hsnd : (code S).snd=(code T).snd := congrArg (fun d : G.Dart => d.snd) heq
    let q := (path T).copy hfst.symm rfl
    have hq : q.IsPath := by simpa [q] using hpath T
    have hqfirst : (path S).getVert 1=q.getVert 1 := by
      simp only [q,getVert_copy]
      exact (hfirst S).trans (hsnd.trans (hfirst T).symm)
    have heqlen : (path S).length=q.length := by
      simp only [q,Walk.length_copy]
      exact Nat.add_right_cancel ((hlen S).trans (hlen T).symm)
    have heqsupport := ExponentialPush.DegreeTwo.support_eq_of_first_step G hdegree
      (path S) q (hpath S) hq heqlen hqfirst
    apply Subtype.ext
    rw [←hsupport S,←hsupport T]
    simpa only [q,Walk.support_copy] using congrArg List.toFinset heqsupport
  have hcard := Fintype.card_le_of_injective code hinj
  simpa only [Fintype.card_coe] using hcard

/-- A uniform bound including the singleton case and empty ambient graphs. -/
theorem connectedSets_card_le (G : SimpleGraph (Fin N))
    (hdegree : ∀ v, G.degree v ≤ 2) (k : ℕ) (hk : 0<k) :
    (connectedSets G k).card ≤ 2*N := by
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
      _ ≤ 2*N := by omega
  · have hk2 : 2≤k := by omega
    calc
      (connectedSets G k).card ≤ Fintype.card G.Dart := connectedSets_card_le_darts G hdegree k hk2
      _ = ∑ v, G.degree v := G.dart_card_eq_sum_degrees
      _ ≤ ∑ _v : Fin N, 2 := Finset.sum_le_sum (fun v _ => hdegree v)
      _ = 2*N := by simp [Nat.mul_comm]

#check @connectedSets_card_le
#print axioms connected_set_spanning_path
#print axioms connectedSets_card_le
end MaxCaterpillar.Overnight.DegreeTwo
