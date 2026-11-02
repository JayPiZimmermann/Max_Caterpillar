import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! A genuine cycle in an indexed interaction graph supplies a nonempty
set of original edges whose consistently oriented differences telescope.
The indexing need not be injective: a simple cycle itself has distinct edges.
-/
set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.ForestMatching
open BigOperators
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

/-- The simple graph of a finite collection of indexed unordered endpoint
pairs. Loops are ignored, and parallel original indices are allowed. -/
def indexedGraph (A : Finset ι) (a b : ι → V) : SimpleGraph V where
  Adj u v := u≠v ∧ ∃ i∈A,(a i=u ∧ b i=v) ∨ (a i=v ∧ b i=u)
  symm := by
    intro u v h
    obtain ⟨huv,i,hi,h⟩ := h
    exact ⟨Ne.symm huv,i,hi,h.symm⟩
  loopless := by intro v h; exact h.1 rfl

lemma indexedGraph_mono {A B : Finset ι} (hAB : A⊆B) (a b : ι→V) :
    indexedGraph A a b≤indexedGraph B a b := by
  intro u v h
  obtain ⟨huv,i,hi,h⟩ := h
  exact ⟨huv,i,hAB hi,h⟩

lemma walk_difference_sum (G : SimpleGraph V) {u v : V} (p : G.Walk u v)
    (x : V → ℝ) : (p.darts.map fun d => x d.fst - x d.snd).sum = x u - x v := by
  induction p with
  | nil => simp
  | cons h p ih => simp only [SimpleGraph.Walk.darts_cons,List.map_cons,List.sum_cons,ih]; ring

/-- Every actual graph cycle has a nonempty collection of original indexed
edges that can be oriented into a zero sum. Parallel original indices are
allowed; only the selected cycle uses distinct underlying graph edges. -/
theorem exists_oriented_cycle_of_not_acyclic (G : SimpleGraph V)
    (A : Finset ι) (a b : ι → V)
    (hrep : ∀ v w, G.Adj v w →
      ∃ i ∈ A, (a i=v ∧ b i=w) ∨ (a i=w ∧ b i=v))
    (hcycle : ¬G.IsAcyclic) :
    ∃ S : Finset ι, S⊆A ∧ S.Nonempty ∧ ∃ reverse : ι→Bool,
      ∀ x : V→ℝ,
        ∑ i in S,(if reverse i then -(x (a i)-x (b i)) else x (a i)-x (b i))=0 := by
  classical
  simp only [SimpleGraph.IsAcyclic,not_forall,not_not] at hcycle
  obtain ⟨v,p,hp⟩ := hcycle
  choose f hfA hf using fun d : G.Dart => hrep d.fst d.snd d.is_adj
  have hedge : ∀ d : G.Dart, (⟦(a (f d),b (f d))⟧ : Sym2 V)=d.edge := by
    intro d
    rcases hf d with h|h
    · simp [SimpleGraph.Dart.edge,h.1,h.2]
    · simp [SimpleGraph.Dart.edge,h.1,h.2,Sym2.eq_swap]
  let D : Finset G.Dart := p.darts.toFinset
  have hinj : ∀ d∈D,∀ e∈D,f d=f e→d=e := by
    intro d hd e he h
    apply List.inj_on_of_nodup_map hp.isCircuit.isTrail.edges_nodup
      (List.mem_toFinset.mp hd) (List.mem_toFinset.mp he)
    rw [←hedge d,←hedge e,h]
  have hD : D.Nonempty := by
    cases p with
    | nil => exact (hp.isCircuit.ne_nil rfl).elim
    | cons h q => exact ⟨⟨(_, _),h⟩,by simp [D]⟩
  let reverse : ι→Bool := fun i =>
    if h : ∃ d∈D,f d=i then decide (a i≠(Classical.choose h).fst) else false
  have hr : ∀ d∈D, reverse (f d)=decide (a (f d)≠d.fst) := by
    intro d hd
    have hex : ∃ e∈D,f e=f d := ⟨d,hd,rfl⟩
    dsimp only [reverse]
    rw [dif_pos hex]
    have he : Classical.choose hex=d :=
      hinj _ (Classical.choose_spec hex).1 _ hd (Classical.choose_spec hex).2
    rw [he]
  have horient : ∀ d∈D,∀ x : V→ℝ,
      (if reverse (f d) then -(x (a (f d))-x (b (f d)))
        else x (a (f d))-x (b (f d)))=x d.fst-x d.snd := by
    intro d hd x
    rw [hr d hd]
    rcases hf d with h|h
    · simp [h.1,h.2]
    · simp [h.1,h.2,Ne.symm d.is_adj.ne]
  refine ⟨D.image f,?_,hD.image f,reverse,?_⟩
  · intro i hi
    obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hi
    exact hfA d
  · intro x
    rw [Finset.sum_image hinj]
    calc
      (∑ d in D,if reverse (f d) then -(x (a (f d))-x (b (f d)))
          else x (a (f d))-x (b (f d)))=
          ∑ d in D,(x d.fst-x d.snd) := Finset.sum_congr rfl (fun d hd => horient d hd x)
      _=(p.darts.map fun d => x d.fst-x d.snd).sum :=
        List.sum_toFinset _ (List.Nodup.of_map _ hp.isCircuit.isTrail.edges_nodup)
      _=0 := by rw [walk_difference_sum]; ring

/-- Concrete indexed-graph form of the cycle selection theorem. -/
theorem indexedGraph_oriented_cycle (A : Finset ι) (a b : ι→V)
    (hcycle : ¬(indexedGraph A a b).IsAcyclic) :
    ∃ S : Finset ι, S⊆A ∧ S.Nonempty ∧ ∃ reverse : ι→Bool,
      ∀ x : V→ℝ,
        ∑ i in S,(if reverse i then -(x (a i)-x (b i)) else x (a i)-x (b i))=0 :=
  exists_oriented_cycle_of_not_acyclic (indexedGraph A a b) A a b
    (fun _ _ h => h.2) hcycle

#print axioms walk_difference_sum
#print axioms indexedGraph_mono
#print axioms exists_oriented_cycle_of_not_acyclic
#print axioms indexedGraph_oriented_cycle

end MaxCaterpillar.ExponentialPush.ForestMatching
