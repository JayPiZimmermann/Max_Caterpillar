import MaxCaterpillar.Fiber.GatingAbstractions.RegularityCoordinates

/-! The fixed observation/free-coordinate decomposition of forty-five weights. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.GatingAbstractions

def splitCoordinatesLinear : Raw ≃ₗ[ℝ] ((Fin 28 → ℝ) × Free) where
  toFun p := (fun i => p (Fin.castAdd 17 i), fun i => p (Fin.natAdd 28 i))
  invFun p := Fin.append p.1 p.2
  left_inv p := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      exact Fin.append_left _ _ j
    · intro j
      exact Fin.append_right _ _ j
  right_inv p := by
    apply Prod.ext
    · funext i
      exact Fin.append_left _ _ i
    · funext i
      exact Fin.append_right _ _ i
  map_add' p q := rfl
  map_smul' s p := rfl

/-- A coordinate rearrangement; both finite real spaces have their usual norms. -/
def splitCoordinates : Raw ≃L[ℝ] ((Fin 28 → ℝ) × Free) :=
  splitCoordinatesLinear.toContinuousLinearEquiv

@[simp] theorem splitCoordinates_apply (p : Raw) :
    splitCoordinates p =
      (fun i : Fin 28 => p (Fin.castAdd 17 i), fun i : Fin 17 => p (Fin.natAdd 28 i)) := rfl

@[simp] theorem splitCoordinates_symm_apply (p : (Fin 28 → ℝ) × Free) :
    splitCoordinates.symm p = Fin.append p.1 p.2 := rfl

#print axioms splitCoordinates
end MaxCaterpillar.Fiber.GatingAbstractions
