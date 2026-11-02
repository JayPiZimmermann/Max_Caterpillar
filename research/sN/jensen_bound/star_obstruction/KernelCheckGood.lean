import MaxCaterpillar.Frontier.StarCertificate.XiKernelCheck
open MaxCaterpillar.Frontier.StarCertificate
theorem good : (true && true) = true := by kernel_bool_check
#print axioms good
