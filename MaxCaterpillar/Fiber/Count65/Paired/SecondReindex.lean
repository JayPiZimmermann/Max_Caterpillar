import MaxCaterpillar.Fiber.SymmetryHomeomorph
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Data.Fintype.Sum

/-! Second-layer block enumeration transports actual paths by a homeomorphism.
No path from a network to its relabeling is assumed. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators
variable {N h k l : ℕ}

def reindexSecond (net : Network N h k) (e : Fin l ≃ Fin k) : Network N h l where
  W₁ := net.W₁
  b₁ := net.b₁
  W₂ i := net.W₂ (e i)
  b₂ i := net.b₂ (e i)
  w₃ i := net.w₃ (e i)
  b₃ := net.b₃

theorem reindexSecond_eval (net : Network N h k) (e : Fin l ≃ Fin k) (x : Point N) :
    (reindexSecond net e).eval x = net.eval x := by
  unfold Network.eval reindexSecond
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

@[simp] theorem reindexSecond_inverse (net : Network N h k) (e : Fin l ≃ Fin k) :
    reindexSecond (reindexSecond net e) e.symm = net := by
  cases net
  simp [reindexSecond]

theorem continuous_reindexSecond (e : Fin l ≃ Fin k) :
    Continuous (fun net : Network N h k => reindexSecond net e) := by
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_W₁,continuous_b₁,?_,?_,?_,continuous_b₃⟩
  · apply continuous_pi
    intro i
    exact (continuous_apply (e i)).comp continuous_W₂
  · apply continuous_pi
    intro i
    exact (continuous_apply (e i)).comp continuous_b₂
  · apply continuous_pi
    intro i
    exact (continuous_apply (e i)).comp continuous_w₃

def reindexSecondHomeomorph (e : Fin l ≃ Fin k) : Network N h k ≃ₜ Network N h l where
  toFun net := reindexSecond net e
  invFun net := reindexSecond net e.symm
  left_inv net := reindexSecond_inverse net e
  right_inv net := reindexSecond_inverse net e.symm
  continuous_toFun := continuous_reindexSecond e
  continuous_invFun := continuous_reindexSecond e.symm

theorem reindexSecond_zeroBiases (net : Network N h k) (e : Fin l ≃ Fin k)
    (hb : net.HasZeroBiases) : (reindexSecond net e).HasZeroBiases := by
  refine ⟨hb.1,?_,hb.2.2⟩
  funext i
  simp [reindexSecond,hb.2.1]

variable [NeZero N]

def reindexSecondFiber (e : Fin l ≃ Fin k) (a : ExactFiber N h k) : ExactFiber N h l :=
  ⟨reindexSecond a.val e, fun x => (reindexSecond_eval a.val e x).trans (a.property x)⟩

def reindexSecondFiberHomeomorph (e : Fin l ≃ Fin k) : ExactFiber N h k ≃ₜ ExactFiber N h l where
  toFun := reindexSecondFiber e
  invFun := reindexSecondFiber e.symm
  left_inv a := Subtype.ext (reindexSecond_inverse a.val e)
  right_inv a := Subtype.ext (reindexSecond_inverse a.val e.symm)
  continuous_toFun := ((continuous_reindexSecond e).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_reindexSecond e.symm).comp continuous_subtype_val).subtype_mk _

theorem joinedIn_reindexSecond {a b : Network N h k}
    (hab : JoinedIn (ExactSet N h k) a b) (e : Fin l ≃ Fin k) :
    JoinedIn (ExactSet N h l) (reindexSecond a e) (reindexSecond b e) := by
  refine ⟨hab.somePath.map (continuous_reindexSecond e),?_⟩
  intro t x
  exact (reindexSecond_eval (hab.somePath t) e x).trans (hab.somePath_mem t x)

theorem joinedIn_reindexSecond_iff (a b : Network N h k) (e : Fin l ≃ Fin k) :
    JoinedIn (ExactSet N h l) (reindexSecond a e) (reindexSecond b e) ↔
      JoinedIn (ExactSet N h k) a b := by
  constructor
  · intro hab
    simpa only [reindexSecond_inverse] using joinedIn_reindexSecond hab e.symm
  · intro hab
    exact joinedIn_reindexSecond hab e

/-- Map a constructed block path back to the original physical indexing. -/
theorem joinedIn_reindexSecond_mapBack (a : Network N h k) (b : Network N h l)
    (e : Fin l ≃ Fin k) (hab : JoinedIn (ExactSet N h l) (reindexSecond a e) b) :
    JoinedIn (ExactSet N h k) a (reindexSecond b e.symm) := by
  simpa only [reindexSecond_inverse] using joinedIn_reindexSecond hab e.symm

variable (S : Finset (Fin k))

/-- Enumerate the selected physical slots first, then their complement. -/
noncomputable def selectedSecondEquiv : Fin (S.card+(k-S.card)) ≃ Fin k := by
  classical
  let eS : Fin S.card ≃ S := (Finset.equivFin S).symm
  let eC : Fin (k-S.card) ≃ {i : Fin k // i ∉ S} :=
    (Fintype.equivFinOfCardEq (by
      simp only [Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe])).symm
  exact finSumFinEquiv.symm.trans ((Equiv.sumCongr eS eC).trans
    (Equiv.sumCompl (fun i : Fin k => i ∈ S)))

theorem selectedSecondEquiv_prefix_mem (i : Fin S.card) :
    selectedSecondEquiv S (Fin.castAdd (k-S.card) i) ∈ S := by
  classical
  simpa [selectedSecondEquiv] using ((Finset.equivFin S).symm i).property

theorem selectedSecondEquiv_suffix_not_mem (i : Fin (k-S.card)) :
    selectedSecondEquiv S (Fin.natAdd S.card i) ∉ S := by
  classical
  unfold selectedSecondEquiv
  simp only [Equiv.trans_apply,finSumFinEquiv_symm_apply_natAdd,Equiv.sumCongr_apply,
    Sum.map_inr,Equiv.sumCompl_apply_inr]
  let eC : Fin (k-S.card) ≃ {j : Fin k // j ∉ S} :=
    (Fintype.equivFinOfCardEq (by
      simp only [Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe])).symm
  exact (eC i).property

theorem selectedSecondEquiv_prefix_onto (j : Fin k) (hj : j ∈ S) :
    ∃ i : Fin S.card, selectedSecondEquiv S (Fin.castAdd (k-S.card) i) = j := by
  classical
  refine ⟨Finset.equivFin S ⟨j,hj⟩,?_⟩
  simp [selectedSecondEquiv]

end MaxCaterpillar.Fiber.Count65.Paired
