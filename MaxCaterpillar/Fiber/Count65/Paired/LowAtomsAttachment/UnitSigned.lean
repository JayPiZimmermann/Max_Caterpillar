import MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment.Source
import MaxCaterpillar.Fiber.Count65.Paired.SwitchingPath

/-! An actual unit comparator and signed baseline attach with spare physical slots. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment

def weightedRow (U : Fin 2 → Fin 2 → ℝ) (s : ℝ) : Fin 6 → ℝ :=
  fun j => baselineRow U j+s*comparisonRow U j

private theorem exists_spare (c p n : Fin 5) : ∃ z : Fin 5, z ≠ c ∧ z ≠ p ∧ z ≠ n := by
  classical
  have hc : ({c,p,n} : Finset (Fin 5)).card ≤ 3 := by
    by_cases hcp : c=p <;> by_cases hcn : c=n <;> by_cases hpn : p=n <;> simp_all <;> omega
  have hz : ∃ z : Fin 5, z ∉ ({c,p,n} : Finset (Fin 5)) := by
    by_contra hh
    push_neg at hh
    have hsub : (Finset.univ : Finset (Fin 5)) ⊆ {c,p,n} := fun i _ => hh i
    have hle := Finset.card_le_of_subset hsub
    simp only [Finset.card_univ,Fintype.card_fin] at hle
    omega
  obtain ⟨z,hz⟩ := hz
  exact ⟨z,by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hz⟩

theorem unit_signed_quotient_joined (a : ExactFiber 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hdet : codeDet U ≠ 0)
    (hU : a.val.W₁ = pairedRows U) (hb : a.val.HasZeroBiases)
    (c p n : Fin 5) (hcp : c ≠ p) (hcn : c ≠ n) (hpn : p ≠ n) (flip : Bool)
    (hwc : a.val.w₃ c = 1) (hwp : a.val.w₃ p = 1) (hwn : a.val.w₃ n = -1)
    (hwo : ∀ i, i ≠ c → i ≠ p → i ≠ n → a.val.w₃ i = 0)
    (hpc : ∀ x, endpointForm U (a.val.W₂ c) x =
      if flip then -endpointForm U (comparisonRow U) x else endpointForm U (comparisonRow U) x)
    (hpp : a.val.W₂ p = weightedRow U (orientationIndicator flip))
    (hpnrow : a.val.W₂ n = -weightedRow U (orientationIndicator flip)) :
    Joined (quotientMk a) (quotientMk (pairedMinimalPoint U hdet)) := by
  classical
  obtain ⟨z,hzc,hzp,hzn⟩ := exists_spare c p n
  let cp : Fin 5 := if flip then z else c
  let cn : Fin 5 := if flip then c else z
  have hcpn : cp ≠ cn := by
    cases flip
    · simpa [cp,cn] using Ne.symm hzc
    · simpa [cp,cn] using hzc
  have hcpp : cp ≠ p := by cases flip <;> simp_all [cp]
  have hcpn' : cp ≠ n := by cases flip <;> simp_all [cp]
  have hcnp : cn ≠ p := by cases flip <;> simp_all [cn]
  have hcnn : cn ≠ n := by cases flip <;> simp_all [cn]
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
  have h4c : e 4 ≠ c := by cases flip <;> simp_all [cp,cn]
  have hwz : a.val.w₃ z = 0 := hwo z hzc hzp hzn
  apply comparator_source_quotient_joined a U hdet hU hb e (orientationIndicator flip)
  · intro i
    fin_cases i
    · change a.val.w₃ (e 0) = 1-orientationIndicator flip
      rw [he₀]
      cases flip <;> simp [cp,orientationIndicator,hwc,hwz]
    · change a.val.w₃ (e 1) = orientationIndicator flip
      rw [he₁]
      cases flip <;> simp [cn,orientationIndicator,hwc,hwz]
    · change a.val.w₃ (e 2) = 1
      rw [he₂]
      exact hwp
    · change a.val.w₃ (e 3) = -1
      rw [he₃]
      exact hwn
    · exact hwo (e 4) h4c h4p h4n
  · intro i hi x
    fin_cases i
    · change a.val.w₃ (e 0) ≠ 0 at hi
      change endpointForm U (a.val.W₂ (e 0)) x = endpointForm U (comparisonRow U) x
      rw [he₀] at hi ⊢
      cases hflip : flip
      · simpa [cp,hflip] using hpc x
      · have hz : a.val.w₃ cp = 0 := by simp [cp,hflip,hwz]
        exact False.elim (hi hz)
    · change a.val.w₃ (e 1) ≠ 0 at hi
      change endpointForm U (a.val.W₂ (e 1)) x = endpointForm U (-comparisonRow U) x
      rw [he₁] at hi ⊢
      rw [endpointForm_neg]
      cases hflip : flip
      · have hz : a.val.w₃ cn = 0 := by simp [cn,hflip,hwz]
        exact False.elim (hi hz)
      · simpa [cn,hflip] using hpc x
    · change endpointForm U (a.val.W₂ (e 2)) x =
        endpointForm U (weightedRow U (orientationIndicator flip)) x
      rw [he₂,hpp]
    · change endpointForm U (a.val.W₂ (e 3)) x =
        endpointForm U (-weightedRow U (orientationIndicator flip)) x
      rw [he₃,hpnrow]
    · exact False.elim (hi (hwo (e 4) h4c h4p h4n))

end MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment
