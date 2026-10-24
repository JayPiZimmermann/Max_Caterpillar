import MaxCaterpillar.CountExp
import MaxCaterpillar.Quotient

open BigOperators MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections MaxNN.Width
namespace MaxCaterpillar

/-- Non-vacuity: for every `r ≥ 1` an expansion with `K = normalizedKeys r` exists. -/
theorem exists_expansion (r : ℕ) (hr : 1 ≤ r) :
    ∃ (d : RealKey (r + 1) → ℝ) (a : Fin (W (r + 1 + 1)) → ℝ),
      ∀ x, Maximum (r + 1 + 1) x =
        ∑ k in normalizedKeys r, d k * realUnitY k x + auxiliary a x := by
  classical
  have h := maximum_mem_dictionary r hr
  rw [dictionary_eq_range] at h
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun ℝ).mp h
  let c' : RealKey (r + 1) → ℝ := fun q => if hq : q ∈ correctionKeys r then c (Sum.inl ⟨q, hq⟩) else 0
  refine ⟨fun k => ∑ q in (correctionKeys r).filter (fun q => normalizedKey q = k), c' q,
    fun j => c (Sum.inr j), fun x => ?_⟩
  have hx := congrFun hc x
  rw [Finset.sum_apply, Fintype.sum_sum_type] at hx
  rw [← hx]
  congr 1
  · simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    have hin : ∀ k ∈ normalizedKeys r,
        ∑ q in (correctionKeys r).filter (fun q => normalizedKey q = k), c' q * realUnitY k x =
        ∑ q in (correctionKeys r).filter (fun q => normalizedKey q = k),
          c' q * realUnitY (normalizedKey q) x := by
      intro k _
      apply Finset.sum_congr rfl
      intro q hq
      rw [(Finset.mem_filter.mp hq).2]
    rw [Finset.sum_congr rfl hin]
    have hfib := Finset.sum_fiberwise_of_maps_to (s := correctionKeys r) (t := normalizedKeys r)
      (g := normalizedKey) (fun q hq => (Finset.mem_image_of_mem normalizedKey hq : _))
      (fun q => c' q * realUnitY (normalizedKey q) x)
    rw [show (∑ k in normalizedKeys r, ∑ q in (correctionKeys r).filter
        (fun q => normalizedKey q = k), c' q * realUnitY (normalizedKey q) x) =
        ∑ q in correctionKeys r, c' q * realUnitY (normalizedKey q) x by convert hfib]
    rw [← Finset.sum_coe_sort (correctionKeys r)]
    apply Finset.sum_congr rfl
    intro q _
    show c (Sum.inl q) * realUnitY q.1 x = c' q.1 * realUnitY (normalizedKey q.1) x
    rw [realUnitY_normalizedKey q.2]
    simp only [c', dif_pos q.2]

/-- The headline is not vacuous: specialized to the full dictionary. -/
example (r : ℕ) (hr : 1 ≤ r) {k : ℕ} (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) :
    (r + 1 + 1).choose k ≤ 6 ^ k * (normalizedKeys r).card := by
  obtain ⟨d, a, h⟩ := exists_expansion r hr
  exact caterpillar_count_exponential r _ subset_rfl d a h hk hkN

end MaxCaterpillar

#print axioms MaxCaterpillar.exists_expansion
#check @MaxCaterpillar.caterpillar_count_exponential
#check @MaxCaterpillar.caterpillar_count_exponential_pow
#print axioms MaxCaterpillar.caterpillar_count_exponential
#print axioms MaxCaterpillar.caterpillar_count_exponential_pow
