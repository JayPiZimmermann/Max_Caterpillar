import MaxCaterpillar.Frontier.StarCertificate.XiCompiledSelectors.Data.Mask12
/-! Twelve bounded checks, each comparing only ten selector rows. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.CompiledSelectorChecks

theorem mask12_block00_checked :
    finAll 10 (fun j => compiledSelectorRowCheck 12 (selectorBlockPermutation 0 j)
      (CompiledSelectorData.row12 (selectorBlockPermutation 0 j)))=true := by
  with_unfolding_all rfl

theorem mask12_block01_checked :
    finAll 10 (fun j => compiledSelectorRowCheck 12 (selectorBlockPermutation 1 j)
      (CompiledSelectorData.row12 (selectorBlockPermutation 1 j)))=true := by
  with_unfolding_all rfl

theorem mask12_block02_checked :
    finAll 10 (fun j => compiledSelectorRowCheck 12 (selectorBlockPermutation 2 j)
      (CompiledSelectorData.row12 (selectorBlockPermutation 2 j)))=true := by
  with_unfolding_all rfl

theorem mask12_block03_checked :
    finAll 10 (fun j => compiledSelectorRowCheck 12 (selectorBlockPermutation 3 j)
      (CompiledSelectorData.row12 (selectorBlockPermutation 3 j)))=true := by
  with_unfolding_all rfl

theorem mask12_block04_checked :
    finAll 10 (fun j => compiledSelectorRowCheck 12 (selectorBlockPermutation 4 j)
      (CompiledSelectorData.row12 (selectorBlockPermutation 4 j)))=true := by
  with_unfolding_all rfl

theorem mask12_block05_checked :
    finAll 10 (fun j => compiledSelectorRowCheck 12 (selectorBlockPermutation 5 j)
      (CompiledSelectorData.row12 (selectorBlockPermutation 5 j)))=true := by
  with_unfolding_all rfl

theorem mask12_block06_checked :
    finAll 10 (fun j => compiledSelectorRowCheck 12 (selectorBlockPermutation 6 j)
      (CompiledSelectorData.row12 (selectorBlockPermutation 6 j)))=true := by
  with_unfolding_all rfl

theorem mask12_block07_checked :
    finAll 10 (fun j => compiledSelectorRowCheck 12 (selectorBlockPermutation 7 j)
      (CompiledSelectorData.row12 (selectorBlockPermutation 7 j)))=true := by
  with_unfolding_all rfl

theorem mask12_block08_checked :
    finAll 10 (fun j => compiledSelectorRowCheck 12 (selectorBlockPermutation 8 j)
      (CompiledSelectorData.row12 (selectorBlockPermutation 8 j)))=true := by
  with_unfolding_all rfl

theorem mask12_block09_checked :
    finAll 10 (fun j => compiledSelectorRowCheck 12 (selectorBlockPermutation 9 j)
      (CompiledSelectorData.row12 (selectorBlockPermutation 9 j)))=true := by
  with_unfolding_all rfl

theorem mask12_block10_checked :
    finAll 10 (fun j => compiledSelectorRowCheck 12 (selectorBlockPermutation 10 j)
      (CompiledSelectorData.row12 (selectorBlockPermutation 10 j)))=true := by
  with_unfolding_all rfl

theorem mask12_block11_checked :
    finAll 10 (fun j => compiledSelectorRowCheck 12 (selectorBlockPermutation 11 j)
      (CompiledSelectorData.row12 (selectorBlockPermutation 11 j)))=true := by
  with_unfolding_all rfl

theorem mask12_block_checked (b : Fin 12) :
    finAll 10 (fun j => compiledSelectorRowCheck 12 (selectorBlockPermutation b j)
      (CompiledSelectorData.row12 (selectorBlockPermutation b j)))=true := by
  fin_cases b
  · exact mask12_block00_checked
  · exact mask12_block01_checked
  · exact mask12_block02_checked
  · exact mask12_block03_checked
  · exact mask12_block04_checked
  · exact mask12_block05_checked
  · exact mask12_block06_checked
  · exact mask12_block07_checked
  · exact mask12_block08_checked
  · exact mask12_block09_checked
  · exact mask12_block10_checked
  · exact mask12_block11_checked

theorem mask12_valid (p : Fin 120) : (CompiledSelectorData.row12 p).Valid 12 p := by
  obtain ⟨b,j,hp⟩ := selectorBlockPermutation_covers p
  have hc := (finAll_eq_true 10 _).mp (mask12_block_checked b) j
  have hv := compiledSelectorRowCheck_sound 12 (selectorBlockPermutation b j) _ hc
  simpa only [hp] using hv

#print axioms mask12_valid

end MaxCaterpillar.Frontier.StarCertificate.CompiledSelectorChecks
