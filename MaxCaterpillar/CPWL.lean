import MaxCaterpillar.Sharing
import MaxNN.CPWL.Representation.Arity

/-! # Every CPWL function has a two-hidden-layer Caterpillar network

`MaxNN.CPWL d` is the class of continuous functions `ℝᵈ → ℝ` agreeing with an
affine function on each piece of a finite closed polyhedral cover of `ℝᵈ`
(`MaxNN/CPWL/Def.lean`).

* `wang_sun`: the Wang–Sun representation theorem. Every `f ∈ CPWL d` is a
  `±1`-signed sum `∑ₜ εₜ max_{d+1}(Aₜ x)` of maxima of `d + 1` affine functions
  (from `MaxNN.hasHingingRep_of_mem_cpwl`).
* `cpwl_two_hidden_layers`: for `d ≥ 2`, composing with `caterpillar_sum_affine`
  gives a network of widths `T · firstWidth (d+1)` and
  `T · (secondWidth (d+1) - 2) + 2`, where `T` is the number of terms of a
  Wang–Sun representation of `f`.
* `cpwl_two_hidden_layers_shared`: the same representation, with the distinct
  affine functions `g₀, …, g_{p-1}` occurring in it collected once. Composing
  with `caterpillar_shared_pieces` gives first width `C(p,2) + p + 1` and second
  width `s · (secondWidth (d+1) - 2) + 2`, where `s ≤ T` is the number of
  distinct argument sets of the terms.

The pieces `g_a` are only the affine functions occurring in the Wang–Sun
representation; that they can be chosen among the affine constituents of `f`
(Koutschan–Moser–Ponomarchuk–Schicho) is not formalized here.
-/

open BigOperators

namespace MaxCaterpillar

/-- **Wang–Sun representation theorem.** Every CPWL function on `ℝᵈ` is a
`±1`-signed sum of maxima of `d + 1` affine functions. -/
theorem wang_sun (d : ℕ) (f : Point d → ℝ) (hf : f ∈ MaxNN.CPWL d) :
    ∃ (T : ℕ) (ε : Fin T → ℝ) (Aw : Fin T → Fin (d + 1) → Fin d → ℝ)
      (Ab : Fin T → Fin (d + 1) → ℝ),
      (∀ t, ε t = 1 ∨ ε t = -1) ∧
      ∀ x, f x = ∑ t, ε t * Maximum (d + 1) (fun i => (∑ l, Aw t i l * x l) + Ab t i) := by
  obtain ⟨T, ε, A, hε, hrep⟩ := MaxNN.hasHingingRep_of_mem_cpwl hf
  exact ⟨T, ε, fun t => (A t).A, fun t => (A t).b, hε, hrep⟩

/-- **CPWL functions, separate Caterpillar blocks.** For `d ≥ 2`, every
`f ∈ CPWL d` has a Wang–Sun representation with some number `T` of terms, and
`f` is computed by a two-hidden-layer network of widths
`T · firstWidth (d+1)` and `T · (secondWidth (d+1) - 2) + 2`. -/
theorem cpwl_two_hidden_layers (d : ℕ) (hd : 2 ≤ d) (f : Point d → ℝ)
    (hf : f ∈ MaxNN.CPWL d) :
    ∃ (T : ℕ) (ε : Fin T → ℝ) (Aw : Fin T → Fin (d + 1) → Fin d → ℝ)
      (Ab : Fin T → Fin (d + 1) → ℝ),
      (∀ t, ε t = 1 ∨ ε t = -1) ∧
      (∀ x, f x = ∑ t, ε t * Maximum (d + 1) (fun i => (∑ l, Aw t i l * x l) + Ab t i)) ∧
      ∃ net : Network d (T * firstWidth (d + 1)) (T * (secondWidth (d + 1) - 2) + 2),
        ∀ x, net.eval x = f x := by
  obtain ⟨T, ε, Aw, Ab, hε, hrep⟩ := wang_sun d f hf
  obtain ⟨r, rfl⟩ : ∃ r, d = r + 1 := ⟨d - 1, by omega⟩
  obtain ⟨net, hnet⟩ := caterpillar_sum_affine r (by omega) Aw Ab ε
  exact ⟨T, ε, Aw, Ab, hε, hrep, net, fun x => (hnet x).trans (hrep x).symm⟩

/-- The all-zero network computes the zero function. -/
theorem Network.eval_zero {N h₁ h₂ : ℕ} (x : Point N) :
    (⟨0, 0, 0, 0, 0, 0⟩ : Network N h₁ h₂).eval x = 0 := by
  unfold Network.eval
  simp

/-- `caterpillar_shared_pieces` for any number `p` of pieces, including `p = 0`. -/
theorem caterpillar_shared_pieces_any {d p T : ℕ} (r : ℕ) (hr : 1 ≤ r)
    (Gw : Fin p → Fin d → ℝ) (Gb : Fin p → ℝ)
    (α : Fin T → Fin (r + 1 + 1) → Fin p) (ε : Fin T → ℝ) :
    ∃ net : Network d (p.choose 2 + p + 1)
      ((imageSets α).card * (secondWidth (r + 1 + 1) - 2) + 2),
      ∀ x, net.eval x = ∑ t, ε t *
        Maximum (r + 1 + 1) (fun i => (∑ l, Gw (α t i) l * x l) + Gb (α t i)) := by
  cases p with
  | zero =>
    have hT : T = 0 := by
      rcases Nat.eq_zero_or_pos T with h | h
      · exact h
      · exact (α ⟨0, h⟩ 0).elim0
    subst hT
    exact ⟨⟨0, 0, 0, 0, 0, 0⟩, fun x => by rw [Network.eval_zero]; rfl⟩
  | succ n => exact caterpillar_shared_pieces r hr Gw Gb α ε

/-- **CPWL functions, shared pieces.** For `d ≥ 2`, every `f ∈ CPWL d` has a
Wang–Sun representation `f = ∑ₜ εₜ max_{d+1}(g_{αₜ 0}, …, g_{αₜ d})` whose `p`
affine functions `g_a(x) = ∑ₗ Gw a l xₗ + Gb a` are pairwise distinct and all
occur, and `f` is computed by a two-hidden-layer network of widths
`C(p,2) + p + 1` and `s · (secondWidth (d+1) - 2) + 2`, where
`s ≤ T` is the number of distinct argument sets `{αₜ i : i}`. -/
theorem cpwl_two_hidden_layers_shared (d : ℕ) (hd : 2 ≤ d) (f : Point d → ℝ)
    (hf : f ∈ MaxNN.CPWL d) :
    ∃ (p T : ℕ) (Gw : Fin p → Fin d → ℝ) (Gb : Fin p → ℝ)
      (α : Fin T → Fin (d + 1) → Fin p) (ε : Fin T → ℝ),
      Function.Injective (fun a => (Gw a, Gb a)) ∧
      (∀ a, ∃ t i, α t i = a) ∧
      (∀ t, ε t = 1 ∨ ε t = -1) ∧
      (∀ x, f x = ∑ t, ε t *
        Maximum (d + 1) (fun i => (∑ l, Gw (α t i) l * x l) + Gb (α t i))) ∧
      ∃ s : ℕ, s = (Finset.univ.image fun t => Finset.univ.image (α t)).card ∧ s ≤ T ∧
        ∃ net : Network d (p.choose 2 + p + 1) (s * (secondWidth (d + 1) - 2) + 2),
          ∀ x, net.eval x = f x := by
  classical
  obtain ⟨T, ε, Aw, Ab, hε, hrep⟩ := wang_sun d f hf
  obtain ⟨r, rfl⟩ : ∃ r, d = r + 1 := ⟨d - 1, by omega⟩
  -- Collect the distinct affine functions occurring in the representation.
  let S : Finset ((Fin (r + 1) → ℝ) × ℝ) :=
    Finset.univ.image fun ti : Fin T × Fin (r + 1 + 1) => (Aw ti.1 ti.2, Ab ti.1 ti.2)
  have hS : ∀ t i, (Aw t i, Ab t i) ∈ S := fun t i =>
    Finset.mem_image_of_mem (fun ti : Fin T × Fin (r + 1 + 1) => (Aw ti.1 ti.2, Ab ti.1 ti.2))
      (Finset.mem_univ (t, i))
  let e : S ≃ Fin S.card := S.equivFin
  let Gw : Fin S.card → Fin (r + 1) → ℝ := fun a => (e.symm a).1.1
  let Gb : Fin S.card → ℝ := fun a => (e.symm a).1.2
  let α : Fin T → Fin (r + 1 + 1) → Fin S.card := fun t i => e ⟨(Aw t i, Ab t i), hS t i⟩
  have hGw : ∀ t i, Gw (α t i) = Aw t i := fun t i => by
    show (e.symm (e _)).1.1 = _
    rw [Equiv.symm_apply_apply]
  have hGb : ∀ t i, Gb (α t i) = Ab t i := fun t i => by
    show (e.symm (e _)).1.2 = _
    rw [Equiv.symm_apply_apply]
  have hrep' : ∀ x, f x = ∑ t, ε t *
      Maximum (r + 1 + 1) (fun i => (∑ l, Gw (α t i) l * x l) + Gb (α t i)) := by
    intro x
    rw [hrep x]
    simp only [hGw, hGb]
  have hinj : Function.Injective (fun a => (Gw a, Gb a)) := by
    intro a b hab
    apply e.symm.injective
    exact Subtype.ext hab
  have hsurj : ∀ a, ∃ t i, α t i = a := by
    intro a
    obtain ⟨⟨t, i⟩, _, hti⟩ := Finset.mem_image.mp (e.symm a).2
    refine ⟨t, i, ?_⟩
    show e ⟨(Aw t i, Ab t i), hS t i⟩ = a
    rw [← e.apply_symm_apply a]
    exact congrArg e (Subtype.ext hti)
  obtain ⟨net, hnet⟩ := caterpillar_shared_pieces_any r (by omega) Gw Gb α ε
  exact ⟨S.card, T, Gw, Gb, α, ε, hinj, hsurj, hε, hrep', _, rfl, card_imageSets_le α, net,
    fun x => (hnet x).trans (hrep' x).symm⟩

end MaxCaterpillar
