import MaxCaterpillar.Frontier.Basic

/-! # Matrix cancellation used by the real quadratic star reduction -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite matrix whose off-diagonal entries cancel with their transposes
has total sum equal to its diagonal sum. Entries are arbitrary real numbers. -/
theorem sum_matrix_eq_diagonal (S : Finset V) (f : V → V → ℝ)
    (hcancel : ∀ i ∈ S,∀ j ∈ S,i≠j → f i j+f j i=0) :
    (∑ i in S,∑ j in S,f i j)=∑ i in S,f i i := by
  have hswap : (∑ i in S,∑ j in S,f i j)=(∑ i in S,∑ j in S,f j i) :=
    Finset.sum_comm
  have hdouble :
      (∑ i in S,∑ j in S,f i j)+(∑ i in S,∑ j in S,f i j)=
        ∑ i in S,∑ j in S,(f i j+f j i) := by
    calc
      _ = (∑ i in S,∑ j in S,f i j)+(∑ i in S,∑ j in S,f j i) :=
        congrArg (fun z => (∑ i in S,∑ j in S,f i j)+z) hswap
      _ = _ := by simp_rw [Finset.sum_add_distrib]
  have hdiagonal : (∑ i in S,∑ j in S,(f i j+f j i))=2*∑ i in S,f i i := by
    calc
      _ = ∑ i in S,2*f i i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_eq_single i]
        · ring
        · intro j _ hji
          exact hcancel i hi j (by assumption) (Ne.symm hji)
        · intro hn
          exact (hn hi).elim
      _ = _ := by rw [Finset.mul_sum]
  linarith only [hdouble,hdiagonal]

/-- Split a finite sum into its actual center entry and the erased center. -/
theorem sum_eq_center_add (f : V → ℝ) (c : V) :
    (∑ i,f i)=f c+∑ i in (Finset.univ : Finset V).erase c,f i := by
  have h := Finset.sum_erase_add (Finset.univ : Finset V) f (Finset.mem_univ c)
  linarith only [h]

/-- If every interaction away from c cancels under transposition, a completely
arbitrary ordered matrix has only its diagonal and center interaction terms. -/
theorem quadratic_matrix_star_split (d : V → V → ℝ) (x : V → ℝ) (c : V)
    (hcancel : ∀ i, i≠c → ∀ j,j≠c → i≠j → d i j+d j i=0) :
    (∑ i,∑ j,d i j*(x i*x j)) =
      d c c*(x c*x c)+
      (∑ i in (Finset.univ : Finset V).erase c,d i i*(x i*x i))+
      x c*(∑ i in (Finset.univ : Finset V).erase c,(d c i+d i c)*x i) := by
  let S : Finset V := Finset.univ.erase c
  have hm : (∑ i in S,∑ j in S,d i j*(x i*x j))=
      ∑ i in S,d i i*(x i*x i) := by
    apply sum_matrix_eq_diagonal
    intro i hi j hj hij
    have he := hcancel i (Finset.mem_erase.mp hi).1 j (Finset.mem_erase.mp hj).1 hij
    calc
      d i j*(x i*x j)+d j i*(x j*x i)=(d i j+d j i)*(x i*x j) := by ring
      _ = 0 := by rw [he,zero_mul]
  have hrow (i : V) : (∑ j,d i j*(x i*x j))=
      d i c*(x i*x c)+∑ j in S,d i j*(x i*x j) := sum_eq_center_add _ c
  rw [sum_eq_center_add (fun i => ∑ j,d i j*(x i*x j)) c,hrow c]
  have hrest : (∑ i in S,∑ j,d i j*(x i*x j))=
      (∑ i in S,d i c*(x i*x c))+(∑ i in S,∑ j in S,d i j*(x i*x j)) := by
    simp_rw [hrow]
    exact Finset.sum_add_distrib
  change d c c*(x c*x c)+(∑ j in S,d c j*(x c*x j))+
    (∑ i in S,∑ j,d i j*(x i*x j))=_
  rw [hrest,hm]
  have hcross : (∑ i in S,d c i*(x c*x i))+(∑ i in S,d i c*(x i*x c))=
      x c*∑ i in S,(d c i+d i c)*x i := by
    rw [← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  dsimp only [S] at hcross ⊢
  linarith only [hcross]

#print axioms sum_matrix_eq_diagonal
#print axioms quadratic_matrix_star_split
end MaxCaterpillar.Frontier.StarCertificate
