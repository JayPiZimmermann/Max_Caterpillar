import MaxCaterpillar.Fiber.GatingAbstractions.RegularityFamilyContinuity
import MaxCaterpillar.Fiber.GatingAbstractions.Defs

set_option autoImplicit false
set_option maxHeartbeats 20000
namespace MaxCaterpillar.Fiber.GatingAbstractions.RegularityFamily
open BigOperators Frontier Filter Topology

lemma aRead_base (c : ℝ) : aRead (base c) = ![0,0,1,-1,0,0] := by
  funext j
  simp [aRead,det,uRead,lu]

lemma bRead_base (c : ℝ) : bRead (base c) = ![0,0,0,0,1,-1] := by
  funext j
  simp [bRead,det,vRead,lv]

lemma aMaxRead_base (c : ℝ) : aMaxRead (base c) = ![1,0,1,-1,0,0] := by
  funext j
  simp only [aMaxRead,aRead_base,base_0,div_one]
  fin_cases j <;>
    norm_num [Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.ext_iff,Fin.coe_ofNat_eq_mod]

lemma bMaxRead_base (c : ℝ) : bMaxRead (base c) = ![0,1,0,0,1,-1] := by
  funext j
  simp only [bMaxRead,bRead_base,base_1,div_one]
  fin_cases j <;>
    norm_num [Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.ext_iff,Fin.coe_ofNat_eq_mod]

lemma negativeRow_base (c : ℝ) : negativeRow (base c) = ![c,1,1,1,1,2] := by
  simp [negativeRow]

lemma positiveRow_base (c : ℝ) : positiveRow (base c) = ![c,2,1,1,2,1] := by
  funext j
  simp only [positiveRow,bMaxRead_base,negativeRow_base,base_8,base_9,div_one]
  fin_cases j <;> norm_num [Matrix.cons_val_zero',Matrix.cons_val_succ']

lemma comparisonRow_base (c : ℝ) : comparisonRow (base c) = pairedOuterCoefficients := by
  funext j
  simp only [comparisonRow,aMaxRead_base,bMaxRead_base,base_10,div_one]
  fin_cases j <;> norm_num [pairedOuterCoefficients,Matrix.cons_val_zero',Matrix.cons_val_succ']

private lemma positiveRow_base_split (c : ℝ) : positiveRow (base c) =
    (fun j => (![0,1,0,0,1,0] : Fin 6 → ℝ) j + GatingAbstractions.offset c j) := by
  rw [positiveRow_base]
  funext j
  fin_cases j
  · change c = 0+c
    ring
  · change (2:ℝ) = 1+1
    norm_num
  · change (1:ℝ) = 0+1
    norm_num
  · change (1:ℝ) = 0+1
    norm_num
  · change (2:ℝ) = 1+1
    norm_num
  · change (1:ℝ) = 0+1
    norm_num

private lemma negativeRow_base_split (c : ℝ) : negativeRow (base c) =
    (fun j => (![0,0,0,0,0,1] : Fin 6 → ℝ) j + GatingAbstractions.offset c j) := by
  rw [negativeRow_base]
  funext j
  fin_cases j
  · change c = 0+c
    ring
  · change (1:ℝ) = 0+1
    norm_num
  · change (1:ℝ) = 0+1
    norm_num
  · change (1:ℝ) = 0+1
    norm_num
  · change (1:ℝ) = 0+1
    norm_num
  · change (2:ℝ) = 1+1
    norm_num

lemma firstRows_base (c : ℝ) : firstRows (base c) = maxFourNet.W₁ := by
  simp [firstRows,lu,lv,maxFourNet]

/-- The rational family passes through every point used by the gating example. -/
theorem familyRaw_base (c : ℝ) : familyRaw (base c) =
    toRaw (MaxCaterpillar.Fiber.GatingAbstractions.family c) := by
  simp only [familyRaw, toRaw, family,
    MaxCaterpillar.Fiber.GatingAbstractions.family, splitNet, pairedNet,
    firstRows_base, positiveRow_base_split, negativeRow_base_split,
    comparisonRow_base, base_8, base_9, base_10]

theorem freeCoordinates_base (c : ℝ) :
    freeCoordinates (toRaw (MaxCaterpillar.Fiber.GatingAbstractions.family c)) = base c := by
  have h := freeCoordinates_familyRaw (base c)
    (by simpa only [base_2] using (one_ne_zero : (1 : ℝ) ≠ 0))
    (by simpa only [base_5] using (one_ne_zero : (1 : ℝ) ≠ 0))
  rw [familyRaw_base] at h
  exact h

theorem familyRaw_freeCoordinates_base (c : ℝ) :
    familyRaw (freeCoordinates (toRaw (MaxCaterpillar.Fiber.GatingAbstractions.family c))) =
      toRaw (MaxCaterpillar.Fiber.GatingAbstractions.family c) := by
  rw [freeCoordinates_base, familyRaw_base]


end MaxCaterpillar.Fiber.GatingAbstractions.RegularityFamily
