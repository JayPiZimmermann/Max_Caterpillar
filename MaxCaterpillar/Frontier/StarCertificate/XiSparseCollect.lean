import MaxCaterpillar.Frontier.StarCertificate.XiSparseProgram
import MaxCaterpillar.Frontier.StarCertificate.XiCachedTargets

/-! # Structural sparse ANOVA evaluation with a generic semantic bridge

Only the fixed program data are checked finitely. This bridge holds for
every integer coefficient table, not just the proposed star certificate.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

def sparseAnovaList (psi : Fin 16→Fin 16→IntegerForm 4) :
    List AnovaEntry→IntegerForm 4
  | [] => fun _ => 0
  | e::es => fun i => e.2.2*psi e.1 e.2.1 i+sparseAnovaList psi es i

def sparseCollect (psi : Fin 16→Fin 16→IntegerForm 4) (t : Fin 80) : IntegerForm 4 :=
  sparseAnovaList psi (anovaProgram t)

theorem sparseAnovaList_eq_sum (psi : Fin 16→Fin 16→IntegerForm 4)
    (es : List AnovaEntry) (i : Fin 4) :
    sparseAnovaList psi es i=(es.map (fun e => e.2.2*psi e.1 e.2.1 i)).sum := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [sparseAnovaList,List.map_cons,List.sum_cons,ih]

theorem canonicalAnovaEntry_injective (S : Finset (Fin 4)) :
    Function.Injective (canonicalAnovaEntry S) := by
  intro a b he
  apply Prod.ext
  · apply maskEquiv.symm.injective
    exact congrArg Prod.fst he
  · apply maskEquiv.symm.injective
    exact congrArg (fun e : AnovaEntry => e.2.1) he

theorem canonicalAnovaEntries_eval (psi : Fin 16→Fin 16→IntegerForm 4)
    (t : Fin 80) (i : Fin 4) :
    (∑ e in canonicalAnovaEntries t, e.2.2*psi e.1 e.2.1 i)=
      collectAnovaCoefficients psi t i := by
  unfold canonicalAnovaEntries collectAnovaCoefficients
  dsimp only
  rw [Finset.sum_image (fun a _ b _ he => canonicalAnovaEntry_injective _ he)]
  change (∑ x in (maskSet (pairS t)).powerset ×ˢ
      ((Finset.univ : Finset (Fin 4)).powerset.filter
        (fun P => P ∩ maskSet (pairS t)=maskSet (pairA t))),
      (canonicalAnovaEntry (maskSet (pairS t)) x).2.2 *
        psi (canonicalAnovaEntry (maskSet (pairS t)) x).1
          (canonicalAnovaEntry (maskSet (pairS t)) x).2.1 i)=_
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro T _
  simp only [canonicalAnovaEntry,Finset.mul_sum]

/-- The sparse list fold equals the original canonical subset/parity sum
for all tables, all eighty targets, and every vector coordinate. -/
theorem sparseCollect_eq_collectAnovaCoefficients
    (psi : Fin 16→Fin 16→IntegerForm 4) (t : Fin 80) (i : Fin 4) :
    sparseCollect psi t i=collectAnovaCoefficients psi t i := by
  unfold sparseCollect
  rw [sparseAnovaList_eq_sum,←List.sum_toFinset _ (anovaProgram_nodup t),
    anovaProgram_entries,canonicalAnovaEntries_eval]

theorem starAnovaIntegerCoefficients_of_sparse_table (s : Fin 15→Sign)
    (psi : Fin 16→Fin 16→IntegerForm 4)
    (hpsi : ∀ T P i, maskedPsiIntegerCoefficients T P s i=psi T P i) :
    starAnovaIntegerCoefficients s=sparseCollect psi := by
  rw [starAnovaIntegerCoefficients_of_shared_table s psi hpsi]
  funext t i
  exact (sparseCollect_eq_collectAnovaCoefficients psi t i).symm

#print axioms sparseCollect_eq_collectAnovaCoefficients
#print axioms starAnovaIntegerCoefficients_of_sparse_table
end MaxCaterpillar.Frontier.StarCertificate
