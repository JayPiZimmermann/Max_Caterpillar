import MaxCaterpillar.Fiber.Retraction

/-! # Connected components of quotients under compatible retractions

A retraction that respects the two equivalence relations descends to their topological
quotients. Pointwise deformation paths descend by composition with the quotient map.
This avoids any additional assumption concerning products of quotient maps or lifting
arbitrary paths from a quotient.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A relation-compatible continuous retraction and pointwise deformation paths induce
a bijection on connected components after taking the specified topological quotients. -/
noncomputable def connectedComponentsEquivOfQuotientRetraction
    (sX : Setoid X) (sY : Setoid Y)
    (r : X → Y) (i : Y → X) (hr : Continuous r) (hi : Continuous i)
    (hr_rel : ∀ x x', sX.r x x' → sY.r (r x) (r x'))
    (hi_rel : ∀ y y', sY.r y y' → sX.r (i y) (i y'))
    (hri : ∀ y, r (i y) = y)
    (hir : ∀ x, Nonempty (Path x (i (r x)))) :
    ConnectedComponents (Quotient sX) ≃ ConnectedComponents (Quotient sY) := by
  let rq : Quotient sX → Quotient sY :=
    Quotient.map' r (fun x x' h => hr_rel x x' h)
  let iq : Quotient sY → Quotient sX :=
    Quotient.map' i (fun y y' h => hi_rel y y' h)
  have hrq : Continuous rq := hr.quotient_map' _
  have hiq : Continuous iq := hi.quotient_map' _
  have hriq : ∀ q, rq (iq q) = q := by
    intro q
    refine Quotient.inductionOn q (fun y => ?_)
    change Quotient.mk sY (r (i y)) = Quotient.mk sY y
    rw [hri]
  have hirq : ∀ q, Nonempty (Path q (iq (rq q))) := by
    intro q
    refine Quotient.inductionOn q (fun x => ?_)
    obtain ⟨p⟩ := hir x
    exact ⟨p.map (continuous_quotient_mk' (s := sX))⟩
  exact connectedComponentsEquivOfPathRetraction rq iq hrq hiq hriq hirq

end MaxCaterpillar.Fiber
