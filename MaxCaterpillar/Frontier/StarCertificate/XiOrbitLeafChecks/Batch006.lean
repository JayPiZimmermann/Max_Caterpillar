import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0048
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0049
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0050
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0051
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0052
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0053
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0054
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0055
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0048
def descriptor132 : OrbitDescriptor := ⟨4, 4, false⟩

theorem checked132 : orbitPatternTransform descriptor132 (Generated.Chunk0048.pattern132) =
    orbitRepresentativePattern descriptor132.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf132 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0048.pattern132 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0048.pattern132) descriptor132 checked132 (hRep descriptor132.representative)

def descriptor133 : OrbitDescriptor := ⟨6, 4, false⟩

theorem checked133 : orbitPatternTransform descriptor133 (Generated.Chunk0048.pattern133) =
    orbitRepresentativePattern descriptor133.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf133 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0048.pattern133 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0048.pattern133) descriptor133 checked133 (hRep descriptor133.representative)

def descriptor134 : OrbitDescriptor := ⟨7, 1, false⟩

theorem checked134 : orbitPatternTransform descriptor134 (Generated.Chunk0048.pattern134) =
    orbitRepresentativePattern descriptor134.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf134 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0048.pattern134 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0048.pattern134) descriptor134 checked134 (hRep descriptor134.representative)

def descriptor135 : OrbitDescriptor := ⟨8, 1, false⟩

theorem checked135 : orbitPatternTransform descriptor135 (Generated.Chunk0048.pattern135) =
    orbitRepresentativePattern descriptor135.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf135 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0048.pattern135 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0048.pattern135) descriptor135 checked135 (hRep descriptor135.representative)

def descriptor136 : OrbitDescriptor := ⟨9, 1, false⟩

theorem checked136 : orbitPatternTransform descriptor136 (Generated.Chunk0048.pattern136) =
    orbitRepresentativePattern descriptor136.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf136 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0048.pattern136 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0048.pattern136) descriptor136 checked136 (hRep descriptor136.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0048.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0048.regionContext := by
  apply Generated.FunctionalChunk0048.valid
  · exact leaf132 hRep
  · exact leaf133 hRep
  · exact leaf134 hRep
  · exact leaf135 hRep
  · exact leaf136 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0048

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0049
def descriptor137 : OrbitDescriptor := ⟨30, 1, false⟩

theorem checked137 : orbitPatternTransform descriptor137 (Generated.Chunk0049.pattern137) =
    orbitRepresentativePattern descriptor137.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf137 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0049.pattern137 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0049.pattern137) descriptor137 checked137 (hRep descriptor137.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0049.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0049.regionContext := by
  apply Generated.FunctionalChunk0049.valid
  · exact leaf137 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0049

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0050
def descriptor138 : OrbitDescriptor := ⟨45, 1, false⟩

theorem checked138 : orbitPatternTransform descriptor138 (Generated.Chunk0050.pattern138) =
    orbitRepresentativePattern descriptor138.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf138 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0050.pattern138 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0050.pattern138) descriptor138 checked138 (hRep descriptor138.representative)

def descriptor139 : OrbitDescriptor := ⟨46, 1, false⟩

theorem checked139 : orbitPatternTransform descriptor139 (Generated.Chunk0050.pattern139) =
    orbitRepresentativePattern descriptor139.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf139 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0050.pattern139 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0050.pattern139) descriptor139 checked139 (hRep descriptor139.representative)

def descriptor140 : OrbitDescriptor := ⟨47, 1, false⟩

theorem checked140 : orbitPatternTransform descriptor140 (Generated.Chunk0050.pattern140) =
    orbitRepresentativePattern descriptor140.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf140 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0050.pattern140 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0050.pattern140) descriptor140 checked140 (hRep descriptor140.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0050.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0050.regionContext := by
  apply Generated.FunctionalChunk0050.valid
  · exact leaf138 hRep
  · exact leaf139 hRep
  · exact leaf140 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0050

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0051
def descriptor141 : OrbitDescriptor := ⟨58, 1, false⟩

theorem checked141 : orbitPatternTransform descriptor141 (Generated.Chunk0051.pattern141) =
    orbitRepresentativePattern descriptor141.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf141 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0051.pattern141 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0051.pattern141) descriptor141 checked141 (hRep descriptor141.representative)

def descriptor142 : OrbitDescriptor := ⟨59, 1, false⟩

theorem checked142 : orbitPatternTransform descriptor142 (Generated.Chunk0051.pattern142) =
    orbitRepresentativePattern descriptor142.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf142 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0051.pattern142 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0051.pattern142) descriptor142 checked142 (hRep descriptor142.representative)

def descriptor143 : OrbitDescriptor := ⟨60, 1, false⟩

theorem checked143 : orbitPatternTransform descriptor143 (Generated.Chunk0051.pattern143) =
    orbitRepresentativePattern descriptor143.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf143 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0051.pattern143 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0051.pattern143) descriptor143 checked143 (hRep descriptor143.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0051.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0051.regionContext := by
  apply Generated.FunctionalChunk0051.valid
  · exact leaf141 hRep
  · exact leaf142 hRep
  · exact leaf143 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0051

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0052
def descriptor144 : OrbitDescriptor := ⟨54, 17, true⟩

theorem checked144 : orbitPatternTransform descriptor144 (Generated.Chunk0052.pattern144) =
    orbitRepresentativePattern descriptor144.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf144 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0052.pattern144 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0052.pattern144) descriptor144 checked144 (hRep descriptor144.representative)

def descriptor145 : OrbitDescriptor := ⟨53, 17, true⟩

theorem checked145 : orbitPatternTransform descriptor145 (Generated.Chunk0052.pattern145) =
    orbitRepresentativePattern descriptor145.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf145 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0052.pattern145 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0052.pattern145) descriptor145 checked145 (hRep descriptor145.representative)

def descriptor146 : OrbitDescriptor := ⟨52, 17, true⟩

theorem checked146 : orbitPatternTransform descriptor146 (Generated.Chunk0052.pattern146) =
    orbitRepresentativePattern descriptor146.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf146 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0052.pattern146 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0052.pattern146) descriptor146 checked146 (hRep descriptor146.representative)

def descriptor147 : OrbitDescriptor := ⟨51, 17, true⟩

theorem checked147 : orbitPatternTransform descriptor147 (Generated.Chunk0052.pattern147) =
    orbitRepresentativePattern descriptor147.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf147 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0052.pattern147 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0052.pattern147) descriptor147 checked147 (hRep descriptor147.representative)

def descriptor148 : OrbitDescriptor := ⟨50, 17, true⟩

theorem checked148 : orbitPatternTransform descriptor148 (Generated.Chunk0052.pattern148) =
    orbitRepresentativePattern descriptor148.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf148 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0052.pattern148 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0052.pattern148) descriptor148 checked148 (hRep descriptor148.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0052.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0052.regionContext := by
  apply Generated.FunctionalChunk0052.valid
  · exact leaf144 hRep
  · exact leaf145 hRep
  · exact leaf146 hRep
  · exact leaf147 hRep
  · exact leaf148 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0052

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0053
def descriptor149 : OrbitDescriptor := ⟨49, 23, true⟩

theorem checked149 : orbitPatternTransform descriptor149 (Generated.Chunk0053.pattern149) =
    orbitRepresentativePattern descriptor149.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf149 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0053.pattern149 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0053.pattern149) descriptor149 checked149 (hRep descriptor149.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0053.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0053.regionContext := by
  apply Generated.FunctionalChunk0053.valid
  · exact leaf149 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0053

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0054
def descriptor150 : OrbitDescriptor := ⟨47, 23, true⟩

theorem checked150 : orbitPatternTransform descriptor150 (Generated.Chunk0054.pattern150) =
    orbitRepresentativePattern descriptor150.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf150 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0054.pattern150 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0054.pattern150) descriptor150 checked150 (hRep descriptor150.representative)

def descriptor151 : OrbitDescriptor := ⟨46, 23, true⟩

theorem checked151 : orbitPatternTransform descriptor151 (Generated.Chunk0054.pattern151) =
    orbitRepresentativePattern descriptor151.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf151 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0054.pattern151 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0054.pattern151) descriptor151 checked151 (hRep descriptor151.representative)

def descriptor152 : OrbitDescriptor := ⟨45, 23, true⟩

theorem checked152 : orbitPatternTransform descriptor152 (Generated.Chunk0054.pattern152) =
    orbitRepresentativePattern descriptor152.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf152 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0054.pattern152 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0054.pattern152) descriptor152 checked152 (hRep descriptor152.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0054.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0054.regionContext := by
  apply Generated.FunctionalChunk0054.valid
  · exact leaf150 hRep
  · exact leaf151 hRep
  · exact leaf152 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0054

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0055
def descriptor153 : OrbitDescriptor := ⟨3, 10, false⟩

theorem checked153 : orbitPatternTransform descriptor153 (Generated.Chunk0055.pattern153) =
    orbitRepresentativePattern descriptor153.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf153 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0055.pattern153 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0055.pattern153) descriptor153 checked153 (hRep descriptor153.representative)

def descriptor154 : OrbitDescriptor := ⟨5, 7, false⟩

theorem checked154 : orbitPatternTransform descriptor154 (Generated.Chunk0055.pattern154) =
    orbitRepresentativePattern descriptor154.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf154 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0055.pattern154 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0055.pattern154) descriptor154 checked154 (hRep descriptor154.representative)

def descriptor155 : OrbitDescriptor := ⟨6, 7, false⟩

theorem checked155 : orbitPatternTransform descriptor155 (Generated.Chunk0055.pattern155) =
    orbitRepresentativePattern descriptor155.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf155 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0055.pattern155 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0055.pattern155) descriptor155 checked155 (hRep descriptor155.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0055.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0055.regionContext := by
  apply Generated.FunctionalChunk0055.valid
  · exact leaf153 hRep
  · exact leaf154 hRep
  · exact leaf155 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0055
