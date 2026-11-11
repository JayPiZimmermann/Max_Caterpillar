import research.sN.overnight_20261103.degree_two.Audit
import research.sN.overnight_20261103.degree_two.ActualTieControls
import research.sN.overnight_20261103.degree_two.SharpAudit
import research.sN.overnight_20261103.degree_two.GraphSharpCheck

/-! Checks-only facade for the exact raw bound, faithful graph scope, and
actual-network controls. No production module imports this driver. -/
set_option autoImplicit false
open MaxCaterpillar

#check @Overnight.DegreeTwo.raw_width_binomial
#check @Overnight.DegreeTwo.raw_width_exponential_real
#check @Overnight.DegreeTwo.Audit.raw_nine_array_bounds
#print axioms Overnight.DegreeTwo.raw_width_binomial
#print axioms Overnight.DegreeTwo.raw_width_exponential
#print axioms Overnight.DegreeTwo.raw_width_exponential_real
#print axioms Overnight.DegreeTwo.Audit.raw_nine_array_bounds
#print axioms Overnight.DegreeTwo.Audit.four_input_nonvacuity
#print axioms ExponentialPush.DegreeTwo.exists_active_second_on_set
#print axioms Overnight.DegreeTwo.twoComponentSets_card_le
#print axioms ExponentialPush.DegreeTwo.Recession.model_computes_max
#check @Overnight.DegreeTwo.raw_width_binomial_sharp
#check @Overnight.DegreeTwo.raw_width_exponential_sharp_real
#print axioms Overnight.DegreeTwo.raw_width_binomial_sharp
#print axioms Overnight.DegreeTwo.raw_width_exponential_sharp_real
#print axioms Overnight.DegreeTwo.normalized_width_binomial_sharp_feeding
#print axioms Overnight.DegreeTwo.SharpAudit.raw_nine_array_sharp_bounds
#print axioms Overnight.DegreeTwo.SharpAudit.normalized_feeding_exact_type
