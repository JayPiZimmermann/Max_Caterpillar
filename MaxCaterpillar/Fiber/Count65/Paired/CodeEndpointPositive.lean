import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpointCodes
import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpointContinuity
import MaxCaterpillar.Fiber.BiasQuotient

/-! # Paths of actual padded endpoints along positive-determinant codes -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open Set

noncomputable def identityCode : Code := ![![1,0],![0,1]]
lemma identityCode_det : codeDet identityCode=1 := by norm_num [identityCode,codeDet]

noncomputable def pairedMinimalZeroPoint (U : Code) (hU : codeDet U≠0) :
    ZeroBiasFiber 4 6 5 := ⟨pairedMinimalPoint U hU,pairedMinimalNet_zeroBias U⟩

noncomputable def pairedMinimalZeroQuotient (U : Code) (hU : codeDet U≠0) :
    ZeroBiasSymmetryQuotient 4 6 5 :=
  Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) (pairedMinimalZeroPoint U hU)

lemma continuous_pairedMinimalZeroPoint_of {X : Type*} [TopologicalSpace X]
    (U : X → Code) (hU : Continuous U) (hne : ∀ x,codeDet (U x)≠0) :
    Continuous (fun x => pairedMinimalZeroPoint (U x) (hne x)) :=
  (continuous_pairedMinimalPoint_of U hU hne).subtype_mk _

lemma continuous_pairedMinimalZeroQuotient_of {X : Type*} [TopologicalSpace X]
    (U : X → Code) (hU : Continuous U) (hne : ∀ x,codeDet (U x)≠0) :
    Continuous (fun x => pairedMinimalZeroQuotient (U x) (hne x)) :=
  continuous_quotient_mk'.comp (continuous_pairedMinimalZeroPoint_of U hU hne)

noncomputable def positiveMinimalQuotient (U : PositiveCode) :
    ZeroBiasSymmetryQuotient 4 6 5 := pairedMinimalZeroQuotient U.val U.property.ne'

lemma continuous_positiveMinimalQuotient : Continuous positiveMinimalQuotient :=
  continuous_pairedMinimalZeroQuotient_of Subtype.val continuous_subtype_val
    (fun U : PositiveCode => U.property.ne')

/-- An actual continuous network-family path, projected through the genuine
allowed-symmetry quotient, joins any two positive-determinant code endpoints. -/
theorem positive_pairedMinimal_quotient_joined (U V : Code)
    (hU : 0 < codeDet U) (hV : 0 < codeDet V) :
    Joined (pairedMinimalZeroQuotient U hU.ne') (pairedMinimalZeroQuotient V hV.ne') := by
  letI := positiveCode_pathConnected
  exact ⟨(PathConnectedSpace.somePath (⟨U,hU⟩ : PositiveCode) ⟨V,hV⟩).map
    continuous_positiveMinimalQuotient⟩

noncomputable def canonicalPairedEndpoint : ZeroBiasSymmetryQuotient 4 6 5 :=
  pairedMinimalZeroQuotient identityCode (by rw [identityCode_det]; norm_num)

theorem positive_pairedMinimal_to_canonical (U : Code) (hU : 0 < codeDet U) :
    Joined (pairedMinimalZeroQuotient U hU.ne') canonicalPairedEndpoint :=
  positive_pairedMinimal_quotient_joined U identityCode hU (by rw [identityCode_det]; norm_num)

#print axioms positive_pairedMinimal_quotient_joined
#print axioms positive_pairedMinimal_to_canonical
end MaxCaterpillar.Fiber.Count65.Paired
