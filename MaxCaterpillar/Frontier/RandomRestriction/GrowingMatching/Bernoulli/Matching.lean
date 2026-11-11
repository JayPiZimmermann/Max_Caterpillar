import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Association
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Selected

/-! # Actual q-matching counts under Bernoulli and downward conditioning

The factorial comes from ordinary q-edge subsets; fixed-label inclusion has
its exact product probability. Downward conditioning can only reduce the
increasing selected-matching event.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
open BigOperators
variable {n q : ℕ}
attribute [local instance] Classical.propDecidable

private theorem mass_union_le_aux {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (E F : Finset (Finset (Fin n))) : mass p (E∪F)≤mass p E+mass p F := by
  have hh := Finset.sum_union_inter (s₁:=E) (s₂:=F) (f:=weight p)
  have hn := mass_nonneg hp0 hp1 (E∩F)
  unfold mass at *
  linarith only [hh,hn]

private theorem mass_biUnion_le_aux {ι : Type*} {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (J : Finset ι) (E : ι→Finset (Finset (Fin n))) :
    mass p (J.biUnion E)≤∑i in J,mass p (E i) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | @insert i J hi ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert hi]
    exact (mass_union_le_aux hp0 hp1 _ _).trans (add_le_add_left ih _)

noncomputable def matchingSets (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (q : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S=>∃B∈matchings G q,matchingVertices B⊆S

@[simp] theorem mem_matchingSets (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (q : ℕ) (S : Finset (Fin n)) :
    S∈matchingSets G q ↔∃B∈matchings G q,matchingVertices B⊆S := by
  simp only [matchingSets,Finset.mem_filter,Finset.mem_univ,true_and]

theorem matchingSets_upper (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ) :
    IsUpperSet (matchingSets G q : Set (Finset (Fin n))) := by
  intro S T hST hS
  obtain ⟨B,hB,hBS⟩ := (mem_matchingSets G q S).mp hS
  exact (mem_matchingSets G q T).mpr ⟨B,hB,hBS.trans hST⟩

/-- Exact finite union bound retaining the actual number of q-matchings. -/
theorem mass_matchingSets_le_matchings {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ) :
    mass p (matchingSets G q)≤((matchings G q).card:ℝ)*p^(2*q) := by
  classical
  have he : matchingSets G q=(matchings G q).biUnion
      (fun B=>Finset.univ.filter fun S : Finset (Fin n)=>matchingVertices B⊆S) := by
    ext S
    simp only [mem_matchingSets,Finset.mem_biUnion,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [he]
  calc
    _ ≤ ∑B in matchings G q,mass p
        (Finset.univ.filter fun S : Finset (Fin n)=>matchingVertices B⊆S) :=
      mass_biUnion_le_aux hp0 hp1 _ _
    _ = ∑_B in matchings G q,p^(2*q) := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [mass_contains,matchingVertices_card G B hB]
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

/-- Ordinary unordered edge counting supplies the crucial q! denominator. -/
theorem mass_matchingSets_le {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ) :
    mass p (matchingSets G q)≤
      (G.edgeFinset.card:ℝ)^q/(q.factorial:ℝ)*p^(2*q) := by
  have hh : ((matchings G q).card:ℝ)≤(G.edgeFinset.card:ℝ)^q/(q.factorial:ℝ) := by
    have hs : ((matchings G q).card:ℝ)≤(G.edgeFinset.card.choose q:ℝ) := by
      exact_mod_cast matchings_card_le_choose (q:=q) G
    exact hs.trans (Nat.choose_le_pow q G.edgeFinset.card)
  exact (mass_matchingSets_le_matchings hp0 hp1 G q).trans
    (mul_le_mul_of_nonneg_right hh (pow_nonneg hp0 _))

/-- The selected matching event remains bounded by the same product count
when conditioned on any nonempty downward event. No rarity factor is lost. -/
theorem condMean_matchingSets_le {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0<mass p D) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ) :
    condMean p D (fun S=>if S∈matchingSets G q then (1:ℝ) else 0)≤
      (G.edgeFinset.card:ℝ)^q/(q.factorial:ℝ)*p^(2*q) := by
  have hf0 : ∀S : Finset (Fin n),0≤(if S∈matchingSets G q then (1:ℝ) else 0) := by
    intro S
    split_ifs <;> norm_num
  have hf : Monotone (fun S : Finset (Fin n)=>if S∈matchingSets G q then (1:ℝ) else 0) := by
    intro S T hST
    change (if S∈matchingSets G q then (1:ℝ) else 0)≤
      (if T∈matchingSets G q then (1:ℝ) else 0)
    by_cases hS : S∈matchingSets G q
    · have hT : T∈matchingSets G q := matchingSets_upper G q hST hS
      rw [if_pos hS,if_pos hT]
    · rw [if_neg hS]
      split_ifs <;> norm_num
  have hh := condMean_le_mean hp0 hp1 D hD hpos _ hf0 hf
  rw [mean_indicator] at hh
  exact hh.trans (mass_matchingSets_le hp0 hp1 G q)

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
