import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.DirectionRule

/-! # Localizing first-layer gates while preserving their original indices -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
open BigOperators
variable {N m h₁ h₂ : ℕ}

noncomputable def firstLinear (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (c : Fin h₁ → ℝ) : Point m :=
  ∑ j, if 0 < lin (net.A j) q then c j • restrict e (net.A j) else 0

noncomputable def localFirst (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) : NormalizedNetwork m h₁ h₂ where
  A j := if lin (net.A j) q = 0 then restrict e (net.A j) else 0
  U k := restrict e (net.U k) + net.firstLinear q e (net.W k)
  W k j := if lin (net.A j) q = 0 then net.W k j else 0
  L := restrict e net.L + net.firstLinear q e net.B
  B j := if lin (net.A j) q = 0 then net.B j else 0
  d := net.d

lemma first_reconstruction (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (c : Fin h₁ → ℝ) (x : Point m) :
    lin (net.firstLinear q e c) x +
      (∑ j, (if lin (net.A j) q = 0 then c j else 0) *
        relu (lin ((net.localFirst q e).A j) x)) =
      ∑ j, c j * net.firstDirection q e j x := by
  classical
  have hlin : lin (net.firstLinear q e c) x =
      ∑ j, if 0 < lin (net.A j) q then c j*lin (restrict e (net.A j)) x else 0 := by
    rw [firstLinear,lin_sum_left]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp [lin_smul_left,lin_zero_left]
  rw [hlin,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rcases lt_trichotomy (lin (net.A j) q) 0 with hneg | hzero | hpos
  · simp [hneg,ne_of_lt hneg,not_lt.mpr hneg.le,localFirst,firstDirection,pick,lin_zero_left,relu]
  · simp [hzero,localFirst,firstDirection,pick]
  · simp [hpos,ne_of_gt hpos,localFirst,firstDirection,pick,lin_zero_left,relu]

lemma localFirst_inner (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (k : Fin h₂) (x : Point m) :
    (net.localFirst q e).inner k x = net.innerDirection q e k x := by
  change lin (restrict e (net.U k) + net.firstLinear q e (net.W k)) x +
    (∑ j, (if lin (net.A j) q = 0 then net.W k j else 0) *
      relu (lin ((net.localFirst q e).A j) x)) = _
  rw [lin_add_left,add_assoc,first_reconstruction]
  rfl

lemma localFirst_output (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (x : Point m) :
    lin (net.localFirst q e).L x +
      (∑ j, (net.localFirst q e).B j * relu (lin ((net.localFirst q e).A j) x)) =
      lin (restrict e net.L) x + ∑ j, net.B j * net.firstDirection q e j x := by
  change lin (restrict e net.L + net.firstLinear q e net.B) x +
    (∑ j, (if lin (net.A j) q = 0 then net.B j else 0) *
      relu (lin ((net.localFirst q e).A j) x)) = _
  rw [lin_add_left,add_assoc,first_reconstruction]

/-- Every retained first row has its exact restricted coefficients. -/
theorem localFirst_row (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (j : Fin h₁) :
    (net.localFirst q e).A j =
      if lin (net.A j) q = 0 then restrict e (net.A j) else 0 := rfl

theorem localFirst_feeding (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (j : Fin h₁)
    (hj : (net.localFirst q e).Feeding j) : net.Feeding j := by
  obtain ⟨k,hk⟩ := hj
  refine ⟨k,?_⟩
  by_contra hz
  exact hk (by simp [localFirst,hz])

#print axioms localFirst_inner
#print axioms localFirst_output
end MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
