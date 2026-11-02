import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Std.Tactic.Ext

/-!
# The finite roles of three moving gates

Two supports of size two whose union has size three have one shared gate,
one exclusive gate each, and two invariant gates. A one-positive/one-negative
sign count on each moving pair fixes the remaining output signs. This is only
finite reindexing; it does not assume or assert an analytic gate normal form.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.PhysicalExtraction

private theorem five_index_equiv (c l r u v : Fin 5)
    (hcl : c ≠ l) (hcr : c ≠ r) (hcu : c ≠ u) (hcv : c ≠ v)
    (hlr : l ≠ r) (hlu : l ≠ u) (hlv : l ≠ v)
    (hru : r ≠ u) (hrv : r ≠ v) (huv : u ≠ v) :
    ∃ e : Fin 5 ≃ Fin 5,
      e 0 = c ∧ e 1 = l ∧ e 2 = r ∧ e 3 = u ∧ e 4 = v := by
  let f : Fin 5 → Fin 5 := ![c,l,r,u,v]
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [f,hcl,hcr,hcu,hcv,hlr,hlu,hlv,hru,hrv,huv,
        Ne.symm hcl,Ne.symm hcr,Ne.symm hcu,Ne.symm hcv,
        Ne.symm hlr,Ne.symm hlu,Ne.symm hlv,
        Ne.symm hru,Ne.symm hrv,Ne.symm huv]
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,rfl⟩
  exact ⟨Equiv.ofBijective f hbij,rfl,rfl,rfl,rfl,rfl⟩

/-- Exact reindexing of the original five gates into their support roles. -/
theorem exists_three_carrier_roles (A B : Finset (Fin 5))
    (hA : A.card = 2) (hB : B.card = 2) (hU : (A ∪ B).card = 3) :
    ∃ e : Fin 5 ≃ Fin 5, A = {e 0,e 1} ∧ B = {e 0,e 2} := by
  classical
  have hI : (A ∩ B).card = 1 := by
    have hh := Finset.card_union_add_card_inter A B
    rw [hA,hB,hU] at hh
    exact Nat.add_left_cancel (show 3 + (A ∩ B).card = 3 + 1 from hh)
  obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hI
  have hAc : (A \ B).card = 1 := by
    have hh := Finset.card_sdiff_add_card_inter A B
    rw [hI,hA] at hh
    exact Nat.add_right_cancel (show (A \ B).card + 1 = 1 + 1 from hh)
  have hBc : (B \ A).card = 1 := by
    have hh := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm B A,hI,hB] at hh
    exact Nat.add_right_cancel (show (B \ A).card + 1 = 1 + 1 from hh)
  obtain ⟨l,hl⟩ := Finset.card_eq_one.mp hAc
  obtain ⟨r,hr⟩ := Finset.card_eq_one.mp hBc
  have hcAB : c ∈ A ∩ B := by rw [hc]; simp
  have hlAB : l ∈ A \ B := by rw [hl]; simp
  have hrBA : r ∈ B \ A := by rw [hr]; simp
  obtain ⟨hcA,hcB⟩ := Finset.mem_inter.mp hcAB
  obtain ⟨hlA,hlB⟩ := Finset.mem_sdiff.mp hlAB
  obtain ⟨hrB,hrA⟩ := Finset.mem_sdiff.mp hrBA
  have hC : ((A ∪ B)ᶜ).card = 2 := by
    rw [Finset.card_compl,hU,Fintype.card_fin]
  obtain ⟨u,v,huv,huvset⟩ := Finset.card_eq_two.mp hC
  have hu : u ∈ (A ∪ B)ᶜ := by rw [huvset]; simp
  have hv : v ∈ (A ∪ B)ᶜ := by rw [huvset]; simp
  have hu' : u ∉ A ∪ B := Finset.mem_compl.mp hu
  have hv' : v ∉ A ∪ B := Finset.mem_compl.mp hv
  have hAcl : A = {c,l} := by
    calc
      A = A \ B ∪ A ∩ B := (Finset.sdiff_union_inter A B).symm
      _ = {c,l} := by rw [hl,hc]; ext x; simp [or_comm]
  have hBcr : B = {c,r} := by
    calc
      B = B \ A ∪ B ∩ A := (Finset.sdiff_union_inter B A).symm
      _ = {c,r} := by rw [hr,Finset.inter_comm B A,hc]; ext x; simp [or_comm]
  obtain ⟨e,he0,he1,he2,_,_⟩ := five_index_equiv c l r u v
    (fun h => hlB (h ▸ hcB))
    (fun h => hrA (h ▸ hcA))
    (fun h => hu' (h ▸ Finset.mem_union_left B hcA))
    (fun h => hv' (h ▸ Finset.mem_union_left B hcA))
    (fun h => hrA (h ▸ hlA))
    (fun h => hu' (h ▸ Finset.mem_union_left B hlA))
    (fun h => hv' (h ▸ Finset.mem_union_left B hlA))
    (fun h => hu' (h ▸ Finset.mem_union_right A hrB))
    (fun h => hv' (h ▸ Finset.mem_union_right A hrB)) huv
  exact ⟨e,by simpa only [he0,he1] using hAcl,
    by simpa only [he0,he2] using hBcr⟩

private theorem positive_count_reindex (s : Fin 5 → Bool) (e : Fin 5 ≃ Fin 5) :
    (Finset.univ.filter fun i => s (e i) = true).card =
      (Finset.univ.filter fun i => s i = true).card := by
  classical
  apply Finset.card_congr (fun i _ => e i)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  · intro a b _ _ hab
    exact e.injective hab
  · intro b hb
    refine ⟨e.symm b,?_,e.apply_symm_apply b⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      simpa only [e.apply_symm_apply] using (Finset.mem_filter.mp hb).2⟩

private def bit (b : Bool) : ℕ := if b = true then 1 else 0

private theorem positive_count_five (s : Fin 5 → Bool) :
    (Finset.univ.filter fun i => s i = true).card =
      bit (s 0) + bit (s 1) + bit (s 2) + bit (s 3) + bit (s 4) := by
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  change bit (s 0) + (bit (s 1) + (bit (s 2) + (bit (s 3) + (bit (s 4) + 0)))) = _
  simp only [Nat.add_assoc,Nat.add_zero]

private theorem pair_positive_count (s : Fin 5 → Bool) (i j : Fin 5) (hij : i ≠ j) :
    (({i,j} : Finset (Fin 5)).filter fun k => s k = true).card =
      bit (s i) + bit (s j) := by
  rw [Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_pair hij]
  rfl

/-- The complete finite sign calculation has only 32 Boolean assignments. -/
private theorem five_sign_pattern : ∀ a b c d e : Bool,
    bit a + bit b + bit c + bit d + bit e = 3 →
    bit a + bit b = 1 → bit a + bit c = 1 →
    b = !a ∧ c = !a ∧ ((d = true ∧ e = a) ∨ (e = true ∧ d = a)) := by
  decide

/-- The actual support reindexing also fixes every output-sign role. The
last two original neurons are ordered with a positive one first. -/
theorem exists_signed_three_carrier_roles (A B : Finset (Fin 5)) (s : Fin 5 → Bool)
    (hA : A.card = 2) (hB : B.card = 2) (hU : (A ∪ B).card = 3)
    (hP : (Finset.univ.filter fun i => s i = true).card = 3)
    (hPA : (A.filter fun i => s i = true).card = 1)
    (hPB : (B.filter fun i => s i = true).card = 1) :
    ∃ e : Fin 5 ≃ Fin 5, A = {e 0,e 1} ∧ B = {e 0,e 2} ∧
      s (e 1) = !(s (e 0)) ∧ s (e 2) = !(s (e 0)) ∧
      s (e 3) = true ∧ s (e 4) = s (e 0) := by
  classical
  obtain ⟨e,heA,heB⟩ := exists_three_carrier_roles A B hA hB hU
  have h01 : e 0 ≠ e 1 := fun h => (by decide : (0 : Fin 5) ≠ 1) (e.injective h)
  have h02 : e 0 ≠ e 2 := fun h => (by decide : (0 : Fin 5) ≠ 2) (e.injective h)
  have hpairA : bit (s (e 0)) + bit (s (e 1)) = 1 := by
    rw [← pair_positive_count s (e 0) (e 1) h01,← heA]
    exact hPA
  have hpairB : bit (s (e 0)) + bit (s (e 2)) = 1 := by
    rw [← pair_positive_count s (e 0) (e 2) h02,← heB]
    exact hPB
  have hcount : bit (s (e 0)) + bit (s (e 1)) + bit (s (e 2)) +
      bit (s (e 3)) + bit (s (e 4)) = 3 := by
    have hc0 : (Finset.univ.filter fun i => s (e i) = true).card = 3 :=
      (positive_count_reindex s e).trans hP
    exact (positive_count_five (fun i => s (e i))).symm.trans hc0
  obtain ⟨h1,h2,hrest⟩ := five_sign_pattern
    (s (e 0)) (s (e 1)) (s (e 2)) (s (e 3)) (s (e 4)) hcount hpairA hpairB
  rcases hrest with hr | hr
  · exact ⟨e,heA,heB,h1,h2,hr.1,hr.2⟩
  · let p : Fin 5 ≃ Fin 5 := Equiv.swap 3 4
    let e' := p.trans e
    have hp0 : p 0 = 0 := by decide
    have hp1 : p 1 = 1 := by decide
    have hp2 : p 2 = 2 := by decide
    have hp3 : p 3 = 4 := by decide
    have hp4 : p 4 = 3 := by decide
    refine ⟨e',?_,?_,?_,?_,?_,?_⟩
    · simpa only [e',Equiv.trans_apply,hp0,hp1] using heA
    · simpa only [e',Equiv.trans_apply,hp0,hp2] using heB
    · simpa only [e',Equiv.trans_apply,hp0,hp1] using h1
    · simpa only [e',Equiv.trans_apply,hp0,hp2] using h2
    · simpa only [e',Equiv.trans_apply,hp3] using hr.1
    · simpa only [e',Equiv.trans_apply,hp0,hp4] using hr.2

#check @exists_three_carrier_roles
#check @exists_signed_three_carrier_roles
#print axioms exists_three_carrier_roles
#print axioms exists_signed_three_carrier_roles
end MaxCaterpillar.Fiber.Count65.PhysicalExtraction
