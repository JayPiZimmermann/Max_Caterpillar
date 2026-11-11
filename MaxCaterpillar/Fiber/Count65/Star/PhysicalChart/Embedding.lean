import MaxCaterpillar.Fiber.Count65.Star.PhysicalChart.Coordinates

/-! # The canonical star charts are genuine physical embeddings

The globally continuous recovery maps use only finitely many ordinary matrix
entries. Their composition with each chart is the natural inclusion of its
parameter fiber into real parameter and actual head data. Consequently the
chart topology agrees with the subspace topology of its physical image.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.Star.PhysicalChart
open MaxCaterpillar.Frontier

abbrev RawParameterData := (ℝ×ℝ)×HeadTopology.Data (featureSpace 1)

/-- The dictionary parameter read from an arbitrary actual network. -/
noncomputable def recoverDictionaryParameter (net : Network 4 6 5) : ℝ := net.W₁ 3 1+1

/-- Global finite-coordinate recovery for the first ordered branch. -/
noncomputable def recoverParameterDataI (o : Fin 3→Bool) (net : Network 4 6 5) : RawParameterData :=
  ((recoverDictionaryParameter net,orientation (o 1)*net.W₂ 1 0),
    recoverHeadData (recoverDictionaryParameter net) net)

/-- Global finite-coordinate recovery for the second ordered branch. -/
noncomputable def recoverParameterDataII (o : Fin 3→Bool) (net : Network 4 6 5) : RawParameterData :=
  ((recoverDictionaryParameter net,orientation (o 0)*net.W₂ 0 1),
    recoverHeadData (recoverDictionaryParameter net) net)

noncomputable def flattenI (o : Fin 3→Bool) (p : BranchIFiber o) : RawParameterData :=
  (p.val.1.val,p.val.2)
noncomputable def flattenII (o : Fin 3→Bool) (p : BranchIIFiber o) : RawParameterData :=
  (p.val.1.val,p.val.2)

lemma continuous_recoverDictionaryParameter : Continuous recoverDictionaryParameter :=
  (((continuous_apply 1).comp ((continuous_apply 3).comp continuous_W₁)).add continuous_const)

lemma continuous_recoverParameterDataI (o : Fin 3→Bool) : Continuous (recoverParameterDataI o) := by
  have hk : Continuous (fun net : Network 4 6 5 => orientation (o 1)*net.W₂ 1 0) :=
    continuous_const.mul ((continuous_apply 0).comp ((continuous_apply 1).comp continuous_W₂))
  exact (continuous_recoverDictionaryParameter.prod_mk hk).prod_mk
    (continuous_recoverHeadData recoverDictionaryParameter id
      continuous_recoverDictionaryParameter continuous_id)

lemma continuous_recoverParameterDataII (o : Fin 3→Bool) : Continuous (recoverParameterDataII o) := by
  have hk : Continuous (fun net : Network 4 6 5 => orientation (o 0)*net.W₂ 0 1) :=
    continuous_const.mul ((continuous_apply 1).comp ((continuous_apply 0).comp continuous_W₂))
  exact (continuous_recoverDictionaryParameter.prod_mk hk).prod_mk
    (continuous_recoverHeadData recoverDictionaryParameter id
      continuous_recoverDictionaryParameter continuous_id)

theorem recoverParameterDataI_chart (o : Fin 3→Bool) (p : BranchIFiber o) :
    recoverParameterDataI o (branchIChart o p)=flattenI o p := by
  unfold recoverParameterDataI recoverDictionaryParameter flattenI
  rw [branchIChart_dictionary_recover,branchIChart_slack_recover,branchIChart_recover_headData]

theorem recoverParameterDataII_chart (o : Fin 3→Bool) (p : BranchIIFiber o) :
    recoverParameterDataII o (branchIIChart o p)=flattenII o p := by
  unfold recoverParameterDataII recoverDictionaryParameter flattenII
  rw [branchIIChart_dictionary_recover,branchIIChart_slack_recover,branchIIChart_recover_headData]

lemma inducing_flattenI (o : Fin 3→Bool) : Inducing (flattenI o) := by
  have hb : Inducing (Prod.map (Subtype.val : ResidualBase 0→ℝ×ℝ)
      (id : HeadTopology.Data (featureSpace 1)→HeadTopology.Data (featureSpace 1))) :=
    inducing_subtype_val.prod_map inducing_id
  exact hb.comp (inducing_subtype_val : Inducing (Subtype.val : BranchIFiber o→_))

lemma inducing_flattenII (o : Fin 3→Bool) : Inducing (flattenII o) := by
  have hb : Inducing (Prod.map (Subtype.val : ResidualBase (-1)→ℝ×ℝ)
      (id : HeadTopology.Data (featureSpace 1)→HeadTopology.Data (featureSpace 1))) :=
    inducing_subtype_val.prod_map inducing_id
  exact hb.comp (inducing_subtype_val : Inducing (Subtype.val : BranchIIFiber o→_))

/-- Each first-branch chart has precisely the physical subspace topology. -/
theorem embedding_branchIChart (o : Fin 3→Bool) : Embedding (branchIChart o) := by
  have he : recoverParameterDataI o ∘ branchIChart o=flattenI o := by
    funext p
    exact recoverParameterDataI_chart o p
  have hi : Inducing (recoverParameterDataI o ∘ branchIChart o) :=
    he.symm ▸ inducing_flattenI o
  exact ⟨inducing_of_inducing_compose (continuous_branchIChart o)
    (continuous_recoverParameterDataI o) hi,branchIChart_injective o⟩

/-- The endpoint-inclusive second branch is a physical embedding as well. -/
theorem embedding_branchIIChart (o : Fin 3→Bool) : Embedding (branchIIChart o) := by
  have he : recoverParameterDataII o ∘ branchIIChart o=flattenII o := by
    funext p
    exact recoverParameterDataII_chart o p
  have hi : Inducing (recoverParameterDataII o ∘ branchIIChart o) :=
    he.symm ▸ inducing_flattenII o
  exact ⟨inducing_of_inducing_compose (continuous_branchIIChart o)
    (continuous_recoverParameterDataII o) hi,branchIIChart_injective o⟩

/-- Homeomorphism onto the actual ordered network image. -/
noncomputable def branchIChartHomeomorph (o : Fin 3→Bool) :
    BranchIFiber o ≃ₜ Set.range (branchIChart o) :=
  Homeomorph.ofEmbedding _ (embedding_branchIChart o)

noncomputable def branchIIChartHomeomorph (o : Fin 3→Bool) :
    BranchIIFiber o ≃ₜ Set.range (branchIIChart o) :=
  Homeomorph.ofEmbedding _ (embedding_branchIIChart o)

@[simp] theorem branchIChartHomeomorph_apply (o : Fin 3→Bool) (p : BranchIFiber o) :
    ((branchIChartHomeomorph o p : Set.range (branchIChart o)) : Network 4 6 5)=branchIChart o p := rfl

@[simp] theorem branchIIChartHomeomorph_apply (o : Fin 3→Bool) (p : BranchIIFiber o) :
    ((branchIIChartHomeomorph o p : Set.range (branchIIChart o)) : Network 4 6 5)=branchIIChart o p := rfl

/-- Exact head-component count in each entire actual ordered chart image. -/
theorem branchI_image_has_two_components (o : Fin 3→Bool) :
    Nonempty (ConnectedComponents (Set.range (branchIChart o)) ≃ Fin 2) := by
  obtain ⟨e⟩ := branchI_total_heads_have_two_components
    (flipValue (o 0)) (flipValue (o 1)) (flipValue (o 2))
  exact ⟨(connectedComponentsEquivOfHomeomorph (branchIChartHomeomorph o).symm).trans e⟩

theorem branchII_image_has_two_components (o : Fin 3→Bool) :
    Nonempty (ConnectedComponents (Set.range (branchIIChart o)) ≃ Fin 2) := by
  obtain ⟨e⟩ := branchII_total_heads_have_two_components
    (flipValue (o 0)) (flipValue (o 1)) (flipValue (o 2))
  exact ⟨(connectedComponentsEquivOfHomeomorph (branchIIChartHomeomorph o).symm).trans e⟩
end MaxCaterpillar.Fiber.Count65.Star.PhysicalChart
