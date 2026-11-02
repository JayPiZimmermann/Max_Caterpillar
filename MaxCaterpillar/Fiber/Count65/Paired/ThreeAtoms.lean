import MaxCaterpillar.Fiber.Count65.Paired.PhysicalAtoms
import MaxCaterpillar.Fiber.Count65.Paired.EffectiveAtoms
import MaxCaterpillar.Fiber.Count65.Paired.SmallAtoms
import MaxCaterpillar.Fiber.Count65.Paired.Cancellation
import MaxCaterpillar.Fiber.Count65.Paired.PairNormalization.Atoms

/-! Three effective comparison atoms extracted from the actual maximum identity. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators

variable {m : ℕ}

abbrev NetworkAtoms (net : Network 4 6 m) :=
  EffectiveAtoms net.w₃ (fun k => net.W₂ k 0) (fun k => net.W₂ k 1)

noncomputable def networkAtomJump (net : Network 4 6 m) (i : NetworkAtoms net) : ℝ :=
  jumpWeights net.w₃ (fun k => net.W₂ k 0) (fun k => net.W₂ k 1) i.val

noncomputable def networkAtomOffset (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (a b : ℝ) (i : NetworkAtoms net) : ℝ :=
  -(codeIntercept net.W₂ U a b i.val+net.W₂ i.val 0*(b-a))/net.W₂ i.val 0

theorem network_effective_atomBalance (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁ = pairedRows U)
    (hb : net.HasZeroBiases) (hnet : ∀ x, net.eval x = Maximum 4 x) (a b : ℝ) :
    Paired65.AtomBalance (networkAtomJump net) (networkAtomOffset net U a b) :=
  effective_atomBalance_of_max a b net.w₃ (codeIntercept net.W₂ U a b)
    (fun k => net.W₂ k 0) (fun k => net.W₂ k 1)
    (network_two_increment_identity net U hU hb hnet a b)

private lemma enumerate_three_with_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hc : Fintype.card ι = 3) (p q : ι) (hpq : p ≠ q) :
    ∃ e : Fin 3 ≃ ι, e 0 = p ∧ e 1 = q := by
  let e₀ : Fin 3 ≃ ι := (Fintype.equivFinOfCardEq hc).symm
  let e₁ : Fin 3 ≃ ι := (Equiv.swap 0 (e₀.symm p)).trans e₀
  have he₁ : e₁ 0 = p := by simp [e₁]
  have hq : (0 : Fin 3) ≠ e₁.symm q := by
    intro hh
    have := congrArg e₁ hh
    simp only [Equiv.apply_symm_apply, he₁] at this
    exact hpq this
  refine ⟨(Equiv.swap 1 (e₁.symm q)).trans e₁, ?_, ?_⟩
  · rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne (by decide) hq, he₁]
  · simp

/-- With exactly three active physical atoms, exactness gives the exhaustive
global target/unit-target/switching alternative. The final branch includes
the actual third jump and both offset identities at every real anchor. -/
theorem network_three_atom_cases (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁ = pairedRows U)
    (hb : net.HasZeroBiases) (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hc : (activeAtoms net.w₃ (fun k => net.W₂ k 0) (fun k => net.W₂ k 1)).card = 3) :
    (∀ a b i, networkAtomOffset net U a b i = 0) ∨
    (∃ i, networkAtomJump net i = 1 ∧ ∀ a b, networkAtomOffset net U a b i = 0) ∨
    (∃ e : Fin 3 ≃ NetworkAtoms net,
      (∀ i, networkAtomJump net (e i) = (![1,1,-1] : Fin 3 → ℝ) i) ∧
      ∀ a b, networkAtomOffset net U a b (e 0) * networkAtomOffset net U a b (e 1) = 0 ∧
        networkAtomOffset net U a b (e 2) =
          networkAtomOffset net U a b (e 0)+networkAtomOffset net U a b (e 1)) := by
  classical
  have hcard : Fintype.card (NetworkAtoms net) = 3 :=
    (effectiveAtoms_card _ _ _).trans hc
  have hbal := network_effective_atomBalance net U hU hb hnet
  have hj : ∀ i : NetworkAtoms net, networkAtomJump net i ≠ 0 := fun i => i.property
  have hcases := three_atom_global_cases (networkAtomJump net)
    (fun x : ℝ × ℝ => networkAtomOffset net U x.1 x.2) hj
    (fun x => hbal x.1 x.2) (le_of_eq hcard)
  rcases hcases with hz | ⟨i, hi, hfi⟩ | ⟨p,q,hpq,hp,hq⟩
  · exact Or.inl (fun a b i => hz (a,b) i)
  · exact Or.inr (Or.inl ⟨i,hi,fun a b => hfi (a,b)⟩)
  · obtain ⟨e,he₀,he₁⟩ := enumerate_three_with_pair hcard p q hpq
    have hj₀ : networkAtomJump net (e 0) = 1 := by rw [he₀,hp]
    have hj₁ : networkAtomJump net (e 1) = 1 := by rw [he₁,hq]
    have hsum := atomBalance_sum_weights _ _ (hbal 0 0)
    have hreindex : (∑ i : Fin 3, networkAtomJump net (e i)) = 1 := by
      rw [Fintype.sum_equiv e _ _ (fun _ => rfl)]
      exact hsum
    have hj₂ : networkAtomJump net (e 2) = -1 := by
      simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
        Fin.succ_zero_eq_one,Fin.succ_one_eq_two] at hreindex
      linarith only [hreindex,hj₀,hj₁]
    have hjump : ∀ i, networkAtomJump net (e i) = (![1,1,-1] : Fin 3 → ℝ) i := by
      intro i
      fin_cases i <;> assumption
    refine Or.inr (Or.inr ⟨e,hjump,?_⟩)
    intro a b
    apply (Paired65.three_relu_offset_identity_iff _ _ _).mp
    intro t
    have hid := Paired65.relu_identity_of_atomBalance _ _ (hbal a b) t
    have heval : (∑ i : Fin 3, networkAtomJump net (e i) *
        relu (t-networkAtomOffset net U a b (e i))) = relu t := by
      exact (Fintype.sum_equiv e _
        (fun i => networkAtomJump net i * relu (t-networkAtomOffset net U a b i))
        (fun _ => rfl)).trans hid
    simpa [Fin.sum_univ_succ,hjump,sub_eq_add_neg,add_assoc] using heval

end MaxCaterpillar.Fiber.Count65.Paired
