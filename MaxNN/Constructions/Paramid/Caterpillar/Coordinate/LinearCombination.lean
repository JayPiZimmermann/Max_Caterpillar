import MaxNN.Constructions.Paramid.Geom.Doubling

namespace MaxNN.Caterpillar

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

theorem smul_sub_smul_mem_of_eq {M : Submodule ℝ F} {f g : F} {a b : ℝ}
    (hab : a = b) (hfg : f - g ∈ M) : a • f - b • g ∈ M := by
  subst b
  simpa only [smul_sub] using M.smul_mem a hfg

theorem smul_sub_smul_mem_of_eq_neg {M : Submodule ℝ F} {f g : F} {a b : ℝ}
    (hab : a = -b) (hfg : f + g ∈ M) : a • f - b • g ∈ M := by
  subst a
  have h := M.smul_mem (-b) hfg
  simpa only [smul_add, neg_smul, sub_eq_add_neg] using h

theorem sub_mem_trans {M : Submodule ℝ F} {f g h : F}
    (hfg : f - g ∈ M) (hgh : g - h ∈ M) : f - h ∈ M := by
  have hadd := M.add_mem hfg hgh
  simpa [sub_eq_add_neg, add_assoc] using hadd

end MaxNN.Caterpillar
