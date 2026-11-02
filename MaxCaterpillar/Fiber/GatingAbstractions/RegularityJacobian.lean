import MaxCaterpillar.Fiber.GatingAbstractions.RegularityJacobianEndpoint

set_option autoImplicit false
namespace MaxCaterpillar.Fiber.GatingAbstractions

/-- Kernel-checked invertible strict derivative at the first merge event. -/
theorem hasStrictFDerivAt_combined_one :
    HasStrictFDerivAt combinedMap (jacEquiv (1 : ℝ)).toContinuousLinearMap
      (toRaw (family 1)) := by
  rw [← combinedD_endpoint_eq 1 (Or.inl rfl)]
  exact strict_combined 1 (by norm_num)

/-- Kernel-checked invertible strict derivative at the second merge event. -/
theorem hasStrictFDerivAt_combined_two :
    HasStrictFDerivAt combinedMap (jacEquiv (2 : ℝ)).toContinuousLinearMap
      (toRaw (family 2)) := by
  rw [← combinedD_endpoint_eq 2 (Or.inr rfl)]
  exact strict_combined 2 (by norm_num)

#print axioms hasStrictFDerivAt_combined_one
#print axioms hasStrictFDerivAt_combined_two
end MaxCaterpillar.Fiber.GatingAbstractions
