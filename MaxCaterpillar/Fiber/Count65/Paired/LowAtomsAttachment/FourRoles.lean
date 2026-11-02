import MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment.UnitSigned

/-! Two target comparison orientations and a signed weighted baseline. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment

theorem two_comparisons_signed_quotient_joined (a : ExactFiber 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hdet : codeDet U ≠ 0)
    (hU : a.val.W₁ = pairedRows U) (hb : a.val.HasZeroBiases)
    (cp cn p n : Fin 5) (h01 : cp ≠ cn) (h02 : cp ≠ p) (h03 : cp ≠ n)
    (h12 : cn ≠ p) (h13 : cn ≠ n) (h23 : p ≠ n) (s : ℝ)
    (hwcp : a.val.w₃ cp = 1-s) (hwcn : a.val.w₃ cn = s)
    (hwp : a.val.w₃ p = 1) (hwn : a.val.w₃ n = -1)
    (hwo : ∀ i, i ≠ cp → i ≠ cn → i ≠ p → i ≠ n → a.val.w₃ i = 0)
    (hcpr : ∀ x, endpointForm U (a.val.W₂ cp) x = endpointForm U (comparisonRow U) x)
    (hcnr : ∀ x, endpointForm U (a.val.W₂ cn) x = -endpointForm U (comparisonRow U) x)
    (hpr : a.val.W₂ p = weightedRow U s) (hnr : a.val.W₂ n = -weightedRow U s) :
    Joined (quotientMk a) (quotientMk (pairedMinimalPoint U hdet)) := by
  classical
  let f : Fin 4 → Fin 5 := ![cp,cn,p,n]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  obtain ⟨e,he⟩ : ∃ e : Equiv.Perm (Fin 5),
      ∀ i : Fin 4, e (Fin.castAdd 1 i) = f i := extend_second_prefix f hf
  have he₀ : e 0 = cp := he 0
  have he₁ : e 1 = cn := he 1
  have he₂ : e 2 = p := he 2
  have he₃ : e 3 = n := he 3
  have h4cp : e 4 ≠ cp := by rw [← he₀]; exact e.injective.ne (by decide)
  have h4cn : e 4 ≠ cn := by rw [← he₁]; exact e.injective.ne (by decide)
  have h4p : e 4 ≠ p := by rw [← he₂]; exact e.injective.ne (by decide)
  have h4n : e 4 ≠ n := by rw [← he₃]; exact e.injective.ne (by decide)
  apply comparator_source_quotient_joined a U hdet hU hb e s
  · intro i
    fin_cases i
    · change a.val.w₃ (e 0) = 1-s
      rw [he₀]; exact hwcp
    · change a.val.w₃ (e 1) = s
      rw [he₁]; exact hwcn
    · change a.val.w₃ (e 2) = 1
      rw [he₂]; exact hwp
    · change a.val.w₃ (e 3) = -1
      rw [he₃]; exact hwn
    · exact hwo (e 4) h4cp h4cn h4p h4n
  · intro i hi x
    fin_cases i
    · change endpointForm U (a.val.W₂ (e 0)) x = endpointForm U (comparisonRow U) x
      rw [he₀]
      exact hcpr x
    · change endpointForm U (a.val.W₂ (e 1)) x = endpointForm U (-comparisonRow U) x
      rw [he₁]
      rw [endpointForm_neg]
      exact hcnr x
    · change endpointForm U (a.val.W₂ (e 2)) x = endpointForm U (weightedRow U s) x
      rw [he₂,hpr]
    · change endpointForm U (a.val.W₂ (e 3)) x = endpointForm U (-weightedRow U s) x
      rw [he₃,hnr]
    · exact False.elim (hi (hwo (e 4) h4cp h4cn h4p h4n))

end MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment
