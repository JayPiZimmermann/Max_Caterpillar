import MaxCaterpillar.Fiber.Count65.SectorQuotient.RootGraphs.Basic
import MaxCaterpillar.Fiber.Mixed65.Construction
import MaxCaterpillar.Fiber.Star65.Construction
import Mathlib.Tactic.NormNum

/-! # Directed root graphs of the actual mixed and star dictionaries -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient
open MaxCaterpillar.Frontier

@[simp] private lemma vec_four_last (a b c d : ℝ) :
    (![a,b,c,d] : Point 4) 3 = d := rfl

@[simp] private lemma fin_four_last_val : ((3 : Fin 4) : ℕ) = 3 := rfl

/-- The mixed moving row has three nonzero coordinates and contributes no root. -/
theorem mixed_directedRootGraph (t : ℝ) (ht : 0 < t) (a b : Fin 4) :
    directedRootGraph (Mixed65.firstRows t) a b ↔ Star.interiorEdge a b := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have ht1 : t + 1 ≠ 0 := by linarith only [ht]
  have htplus : 1 + t ≠ 0 := by linarith only [ht]
  have htminus : -1 + -t ≠ 0 := by linarith only [ht]
  fin_cases a <;> fin_cases b <;>
    norm_num [directedRootGraph,IsDirectedRootRow,Mixed65.firstRows,
      Star.interiorEdge,Fin.exists_fin_succ,Fin.forall_fin_succ,Fin.ext_iff,
        Matrix.cons_val_zero',Matrix.cons_val_succ',ht,ht0,ht1,htplus,htminus]
  all_goals norm_num [Fin.ext_iff]

/-- The star moving row becomes a fourth directed root precisely at r=1. -/
theorem star_directedRootGraph (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (a b : Fin 4) :
    directedRootGraph (Star65.firstRows r) a b ↔
      if r = 1 then Star.endpointEdge a b else Star.interiorEdge a b := by
  by_cases h : r = 1
  · subst r
    fin_cases a <;> fin_cases b <;>
      norm_num [directedRootGraph,IsDirectedRootRow,Star65.firstRows,
        Star.interiorEdge,Star.endpointEdge,Fin.exists_fin_succ,Fin.forall_fin_succ,Fin.ext_iff,
        Matrix.cons_val_zero',Matrix.cons_val_succ']
  · have hr0 : r ≠ 0 := ne_of_gt hr
    have hrn : r - 1 ≠ 0 := sub_ne_zero.mpr h
    have hrlt : r < 1 := lt_of_le_of_ne hr1 h
    fin_cases a <;> fin_cases b <;>
      norm_num [directedRootGraph,IsDirectedRootRow,Star65.firstRows,
        Star.interiorEdge,Star.endpointEdge,Fin.exists_fin_succ,Fin.forall_fin_succ,Fin.ext_iff,
        Matrix.cons_val_zero',Matrix.cons_val_succ',
        h,hr,hr0,hrn]
    all_goals norm_num [Fin.ext_iff]

end MaxCaterpillar.Fiber.Count65.SectorQuotient
