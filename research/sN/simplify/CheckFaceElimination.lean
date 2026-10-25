import MaxNN.Constructions.Paramid.Geom.Faces

set_option autoImplicit false

open FiniteDimensional
open MaxNN.ParamidGeom MaxNN.ParamidGeom.Faces

-- The stronger theorem used by the simplified proof.
example {m : ℕ} (U : Submodule ℝ (Fin m → ℝ))
    {𝔉 : Set (Finset (Fin m → ℝ))} (h𝔉 : FaceClosed 𝔉)
    {d : ℕ} (hd : d < finrank ℝ U) {g : (Fin m → ℝ) → ℝ}
    (hgF : g ∈ FSpan 𝔉) (hgL : g ∈ LSpan m d) : g ∈ GSpanRel 𝔉 U :=
  mem_GSpanRel_of_lt_finrank U h𝔉 hd hgF hgL

-- Exact historical compatibility statement, without changing its hypotheses.
example {m : ℕ} {𝔉 : Set (Finset (Fin m → ℝ))}
    (U : Submodule ℝ (Fin m → ℝ)) (h𝔉 : FaceClosed 𝔉)
    {d : ℕ} (hd : d < finrank ℝ U) {g : (Fin m → ℝ) → ℝ}
    (hgF : g ∈ FSpan 𝔉) (hgL : g ∈ LSpan m d) :
    g ∈ GSpanRel 𝔉 U ⊔ LSpan m 0 :=
  mem_GSpanRel_sup_of_lt_finrank U h𝔉 hd hgF hgL

#print axioms MaxNN.ParamidGeom.Faces.mem_GSpanRel_of_lt_finrank
#print axioms MaxNN.ParamidGeom.Faces.mem_GSpanRel_sup_of_lt_finrank
#print axioms MaxNN.ParamidGeom.Faces.face_lemma_rel
#print axioms MaxNN.ParamidGeom.Faces.face_lemma_rel_proper
