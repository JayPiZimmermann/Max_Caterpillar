import MaxCaterpillar.Frontier.RandomRestriction.BraidCoinColumn
import Mathlib.Tactic

/-! Arbitrary-arity actual braid-row aggregation, research only. -/
set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.ActualBraid
open BigOperators Frontier Frontier.RandomRestriction
open NormalizedNetwork
variable {N h₁ h₂ : ℕ}

abbrev Pair (N : ℕ) := {p : Fin N × Fin N // p.1 < p.2}
def left (p : Pair N) : Fin N := p.val.1
def right (p : Pair N) : Fin N := p.val.2

theorem pair_distinct (p : Pair N) : left p ≠ right p := ne_of_lt p.property

theorem pair_ext_of_set_eq (p q : Pair N)
    (h : ({left p,right p} : Finset (Fin N))={left q,right q}) : p=q := by
  have hp : left p=left q ∨ left p=right q := by
    have hm : left p ∈ ({left q,right q} : Finset (Fin N)) := h ▸ (by simp)
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
  have hr : right p=left q ∨ right p=right q := by
    have hm : right p ∈ ({left q,right q} : Finset (Fin N)) := h ▸ (by simp)
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
  have hpl := p.property
  have hql := q.property
  change left p < right p at hpl
  change left q < right q at hql
  have he1 : left p=left q := by
    rcases hp with hp|hp
    · exact hp
    · rcases hr with hr|hr
      · rw [hp,hr] at hpl
        exact False.elim ((not_lt_of_ge (le_of_lt hql)) hpl)
      · rw [hp,hr] at hpl
        exact False.elim ((lt_irrefl _) hpl)
  have he2 : right p=right q := by
    rcases hr with hr|hr
    · rw [he1,hr] at hpl
      exact False.elim ((lt_irrefl _) hpl)
    · exact hr
  apply Subtype.ext
  exact Prod.ext he1 he2

/-- Nonzero rows of support at most two have a unique oriented endpoint pair;
zero rows are treated separately, so no artificial N>=2 assumption is needed. -/
theorem exists_pair_of_nonzero (a : Point N) (hsum : ∑ i,a i=0)
    (hcard : (rowSupport a).card≤2) (hne : a≠0) :
    ∃ p : Pair N, rowSupport a={left p,right p} := by
  classical
  have hs : ∑ i in rowSupport a,a i=0 := by
    rw [←hsum]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    exact not_not.mp (by simpa only [mem_rowSupport] using hi)
  have hex : (rowSupport a).Nonempty := by
    by_contra he
    apply hne
    funext i
    have hi : i ∉ rowSupport a := fun hi => he ⟨i,hi⟩
    simpa only [mem_rowSupport,not_not] using hi
  have htwo : (rowSupport a).card=2 := by
    apply Nat.le_antisymm hcard
    by_contra hh
    have hone : (rowSupport a).card≤1 := Nat.le_of_lt_succ (not_le.mp hh)
    obtain ⟨i,hi⟩ := hex
    have he : ∑ j in rowSupport a,a j=a i := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        exact False.elim (hji ((Finset.card_le_one.mp hone) j hj i hi))
      · intro hn
        exact False.elim (hn hi)
    rw [he] at hs
    exact ((mem_rowSupport a i).mp hi) hs
  obtain ⟨i,j,hij,heq⟩ := Finset.card_eq_two.mp htwo
  rcases lt_or_gt_of_ne hij with hlt|hlt
  · exact ⟨⟨(i,j),hlt⟩,heq⟩
  · refine ⟨⟨(j,i),hlt⟩,?_⟩
    simpa [left,right,Finset.pair_comm] using heq

noncomputable def rowAbsCoefficient (a : Point N) (p : Pair N) : ℝ :=
  if rowSupport a={left p,right p} then |a (left p)| else 0

theorem lin_root (p : Pair N) (x : Point N) :
    lin (braidRoot (left p) (right p)) x=x (left p)-x (right p) := by
  simp [braidRoot,lin,unitVec,sub_mul,Finset.sum_sub_distrib]

theorem abs_row_decomposition (a : Point N) (hsum : ∑ i,a i=0)
    (hcard : (rowSupport a).card≤2) (x : Point N) :
    |lin a x|=∑ p : Pair N,rowAbsCoefficient a p*|x (left p)-x (right p)| := by
  classical
  by_cases hz : a=0
  · subst a
    simp [rowAbsCoefficient,rowSupport,lin]
  obtain ⟨p,hp⟩ := exists_pair_of_nonzero a hsum hcard hz
  have hrow := row_eq_root_smul a (left p) (right p) (pair_distinct p) hsum hp.le
  have hl : lin a x=a (left p)*(x (left p)-x (right p)) := by
    calc
      lin a x=lin (a (left p)•braidRoot (left p) (right p)) x :=
        congrArg (fun b : Point N => lin b x) hrow
      _ = _ := by rw [lin_smul_left,lin_root]
  rw [hl,abs_mul]
  symm
  calc
    _ = rowAbsCoefficient a p*|x (left p)-x (right p)| := by
      apply Finset.sum_eq_single p
      · intro q _ hqp
        have hn : rowSupport a≠{left q,right q} := by
          intro hq
          exact hqp ((pair_ext_of_set_eq p q (hp.symm.trans hq)).symm)
        simp [rowAbsCoefficient,hn]
      · simp
    _ = _ := by simp [rowAbsCoefficient,hp]

lemma relu_half_abs (t : ℝ) : relu t=(t+|t|)/2 := by
  rcases le_total 0 t with ht|ht
  · rw [relu_of_nonneg ht,abs_of_nonneg ht];ring
  · rw [relu_of_nonpos ht,abs_of_nonpos ht];ring

noncomputable def coefficient (A : Fin h₁→Point N) (W : Fin h₁→ℝ)
    (p : Pair N) : ℝ := ∑ j,W j*rowAbsCoefficient (A j) p

/-- Exact cancellation among all original parallel rows is retained. -/
theorem coefficient_eq_original (A : Fin h₁→Point N) (W : Fin h₁→ℝ)
    (p : Pair N) :
    coefficient A W p= -braidEdgeWeight A W (left p) (right p) := by
  classical
  simp [coefficient,rowAbsCoefficient,braidEdgeWeight,braidEdgeRows,
    Finset.sum_filter,mul_ite]

noncomputable def head (U : Point N) (A : Fin h₁→Point N)
    (W : Fin h₁→ℝ) : Point N :=
  U+(1/2:ℝ)•(∑ j,W j•A j)-
    (1/2:ℝ)•(∑ p : Pair N,coefficient A W p•braidRoot (left p) (right p))

lemma weighted_relu_half {ι : Type*} [Fintype ι] (c t : ι→ℝ) :
    (∑ i,c i*relu (t i))=((∑ i,c i*t i)+(∑ i,c i*|t i|))/2 := by
  simp only [relu_half_abs,←mul_div_assoc,mul_add,Finset.sum_div,
    Finset.sum_add_distrib]
  rw [←Finset.sum_div,Finset.sum_add_distrib]

lemma lin_weighted_rows (A : Fin h₁→Point N) (W : Fin h₁→ℝ) (x : Point N) :
    lin (∑ j,W j•A j) x=∑ j,W j*lin (A j) x := by
  rw [lin_sum_left]
  apply Finset.sum_congr rfl
  intro j _
  exact lin_smul_left _ _ _

lemma weighted_abs_rows (A : Fin h₁→Point N) (W : Fin h₁→ℝ)
    (hsum : ∀ j,∑ i,A j i=0) (hcard : ∀ j,(rowSupport (A j)).card≤2)
    (x : Point N) :
    (∑ j,W j*|lin (A j) x|)=
      ∑ p : Pair N,coefficient A W p*|x (left p)-x (right p)| := by
  simp_rw [abs_row_decomposition _ (hsum _) (hcard _) x,
    Finset.mul_sum,coefficient,Finset.sum_mul,mul_assoc]
  exact Finset.sum_comm

lemma lin_head (U : Point N) (A : Fin h₁→Point N)
    (W : Fin h₁→ℝ) (x : Point N) :
    lin (head U A W) x=lin U x+(1/2:ℝ)*(∑ j,W j*lin (A j) x)-
      (1/2:ℝ)*(∑ p : Pair N,coefficient A W p*(x (left p)-x (right p))) := by
  unfold head
  simp only [sub_eq_add_neg,lin_add_left,lin_neg_left,lin_smul_left,lin_sum_left,lin_root]

/-- Every original parallel row and arbitrary skip is accounted for pointwise,
with aggregated signed coefficients and a real corrected head. -/
theorem linear_combination_canonical (U : Point N) (A : Fin h₁→Point N)
    (W : Fin h₁→ℝ) (hsum : ∀ j,∑ i,A j i=0)
    (hcard : ∀ j,(rowSupport (A j)).card≤2) (x : Point N) :
    lin U x+(∑ j,W j*relu (lin (A j) x))=
      lin (head U A W) x+
        ∑ p : Pair N,coefficient A W p*relu (x (left p)-x (right p)) := by
  rw [lin_head,weighted_relu_half W (fun j => lin (A j) x),
    weighted_abs_rows A W hsum hcard x,
    weighted_relu_half (coefficient A W) (fun p => x (left p)-x (right p))]
  ring

/-- Correcting the head preserves its complete coordinate sum, including the
output head's unit translation slope. -/
theorem head_sum (U : Point N) (A : Fin h₁→Point N)
    (W : Fin h₁→ℝ) (hsum : ∀ j,∑ i,A j i=0)
    (hcard : ∀ j,(rowSupport (A j)).card≤2) :
    (∑ i,head U A W i)=∑ i,U i := by
  have h := linear_combination_canonical U A W hsum hcard (diag 1)
  simp only [lin_diag,hsum,zero_mul,relu_of_nonneg (le_refl (0:ℝ)),mul_zero,
    Finset.sum_const_zero,add_zero,diag,sub_self] at h
  simpa using h.symm

noncomputable def canonicalEval (net : NormalizedNetwork N h₁ h₂) (x : Point N) : ℝ :=
  lin (head net.L net.A net.B) x+
    (∑ p : Pair N,coefficient net.A net.B p*relu (x (left p)-x (right p)))+
    ∑ k,net.d k*relu (lin (head (net.U k) net.A (net.W k)) x+
      ∑ p : Pair N,coefficient net.A (net.W k) p*relu (x (left p)-x (right p)))

/-- Actual normalized networks, at every arity and with all original second
indices retained, equal their canonical oriented-pair presentation. -/
theorem eval_eq_canonical (net : NormalizedNetwork N h₁ h₂)
    (hnorm : net.TranslationNormalized)
    (hcard : ∀ j,(rowSupport (net.A j)).card≤2) (x : Point N) :
    net.eval x=canonicalEval net x := by
  unfold NormalizedNetwork.eval canonicalEval
  rw [linear_combination_canonical net.L net.A net.B hnorm.1 hcard x]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  exact linear_combination_canonical (net.U k) net.A (net.W k) hnorm.1 hcard x

noncomputable def activeEdges (A : Fin h₁→Point N) (W : Fin h₁→ℝ) : Finset (Pair N) :=
  Finset.univ.filter fun p => coefficient A W p≠0

@[simp] theorem mem_activeEdges (A : Fin h₁→Point N) (W : Fin h₁→ℝ) (p : Pair N) :
    p∈activeEdges A W ↔ coefficient A W p≠0 := by
  classical
  simp [activeEdges]

theorem activeEdges_original (A : Fin h₁→Point N) (W : Fin h₁→ℝ) (p : Pair N) :
    p∈activeEdges A W ↔ braidEdgeWeight A W (left p) (right p)≠0 := by
  rw [mem_activeEdges,coefficient_eq_original,neg_ne_zero]

theorem sum_activeEdges (A : Fin h₁→Point N) (W : Fin h₁→ℝ) (f : Pair N→ℝ) :
    (∑ p in activeEdges A W,coefficient A W p*f p)=∑ p,coefficient A W p*f p := by
  classical
  rw [activeEdges,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : coefficient A W p=0 <;> simp [hp]

theorem linear_combination_active (U : Point N) (A : Fin h₁→Point N)
    (W : Fin h₁→ℝ) (hsum : ∀ j,∑ i,A j i=0)
    (hcard : ∀ j,(rowSupport (A j)).card≤2) (x : Point N) :
    lin U x+(∑ j,W j*relu (lin (A j) x))=
      lin (head U A W) x+
        ∑ p in activeEdges A W,coefficient A W p*relu (x (left p)-x (right p)) := by
  rw [sum_activeEdges]
  exact linear_combination_canonical U A W hsum hcard x


#print axioms abs_row_decomposition
#print axioms coefficient_eq_original
#print axioms linear_combination_canonical
#print axioms head_sum
#print axioms eval_eq_canonical

end MaxCaterpillar.ExponentialPush.ActualBraid
