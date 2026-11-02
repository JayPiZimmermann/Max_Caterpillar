import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0064
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0065
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0066
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0067
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0068
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0069
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0070
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0071
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0064
def descriptor184 : OrbitDescriptor := ⟨32, 1, false⟩

theorem checked184 : orbitPatternTransform descriptor184 (Generated.Chunk0064.pattern184) =
    orbitRepresentativePattern descriptor184.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf184 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0064.pattern184 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0064.pattern184) descriptor184 checked184 (hRep descriptor184.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0064.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0064.regionContext := by
  apply Generated.FunctionalChunk0064.valid
  · exact leaf184 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0064

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0065
def descriptor185 : OrbitDescriptor := ⟨49, 1, false⟩

theorem checked185 : orbitPatternTransform descriptor185 (Generated.Chunk0065.pattern185) =
    orbitRepresentativePattern descriptor185.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf185 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0065.pattern185 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0065.pattern185) descriptor185 checked185 (hRep descriptor185.representative)

def descriptor186 : OrbitDescriptor := ⟨61, 1, false⟩

theorem checked186 : orbitPatternTransform descriptor186 (Generated.Chunk0065.pattern186) =
    orbitRepresentativePattern descriptor186.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf186 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0065.pattern186 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0065.pattern186) descriptor186 checked186 (hRep descriptor186.representative)

def descriptor187 : OrbitDescriptor := ⟨49, 17, true⟩

theorem checked187 : orbitPatternTransform descriptor187 (Generated.Chunk0065.pattern187) =
    orbitRepresentativePattern descriptor187.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf187 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0065.pattern187 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0065.pattern187) descriptor187 checked187 (hRep descriptor187.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0065.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0065.regionContext := by
  apply Generated.FunctionalChunk0065.valid
  · exact leaf185 hRep
  · exact leaf186 hRep
  · exact leaf187 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0065

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0066
def descriptor188 : OrbitDescriptor := ⟨48, 17, true⟩

theorem checked188 : orbitPatternTransform descriptor188 (Generated.Chunk0066.pattern188) =
    orbitRepresentativePattern descriptor188.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf188 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0066.pattern188 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0066.pattern188) descriptor188 checked188 (hRep descriptor188.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0066.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0066.regionContext := by
  apply Generated.FunctionalChunk0066.valid
  · exact leaf188 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0066

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0067
def descriptor189 : OrbitDescriptor := ⟨44, 23, true⟩

theorem checked189 : orbitPatternTransform descriptor189 (Generated.Chunk0067.pattern189) =
    orbitRepresentativePattern descriptor189.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf189 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0067.pattern189 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0067.pattern189) descriptor189 checked189 (hRep descriptor189.representative)

def descriptor190 : OrbitDescriptor := ⟨43, 23, true⟩

theorem checked190 : orbitPatternTransform descriptor190 (Generated.Chunk0067.pattern190) =
    orbitRepresentativePattern descriptor190.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf190 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0067.pattern190 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0067.pattern190) descriptor190 checked190 (hRep descriptor190.representative)

def descriptor191 : OrbitDescriptor := ⟨42, 23, true⟩

theorem checked191 : orbitPatternTransform descriptor191 (Generated.Chunk0067.pattern191) =
    orbitRepresentativePattern descriptor191.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf191 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0067.pattern191 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0067.pattern191) descriptor191 checked191 (hRep descriptor191.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0067.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0067.regionContext := by
  apply Generated.FunctionalChunk0067.valid
  · exact leaf189 hRep
  · exact leaf190 hRep
  · exact leaf191 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0067

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0068
def descriptor192 : OrbitDescriptor := ⟨4, 10, false⟩

theorem checked192 : orbitPatternTransform descriptor192 (Generated.Chunk0068.pattern192) =
    orbitRepresentativePattern descriptor192.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf192 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0068.pattern192 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0068.pattern192) descriptor192 checked192 (hRep descriptor192.representative)

def descriptor193 : OrbitDescriptor := ⟨6, 10, false⟩

theorem checked193 : orbitPatternTransform descriptor193 (Generated.Chunk0068.pattern193) =
    orbitRepresentativePattern descriptor193.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf193 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0068.pattern193 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0068.pattern193) descriptor193 checked193 (hRep descriptor193.representative)

def descriptor194 : OrbitDescriptor := ⟨7, 7, false⟩

theorem checked194 : orbitPatternTransform descriptor194 (Generated.Chunk0068.pattern194) =
    orbitRepresentativePattern descriptor194.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf194 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0068.pattern194 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0068.pattern194) descriptor194 checked194 (hRep descriptor194.representative)

def descriptor195 : OrbitDescriptor := ⟨8, 7, false⟩

theorem checked195 : orbitPatternTransform descriptor195 (Generated.Chunk0068.pattern195) =
    orbitRepresentativePattern descriptor195.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf195 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0068.pattern195 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0068.pattern195) descriptor195 checked195 (hRep descriptor195.representative)

def descriptor196 : OrbitDescriptor := ⟨9, 7, false⟩

theorem checked196 : orbitPatternTransform descriptor196 (Generated.Chunk0068.pattern196) =
    orbitRepresentativePattern descriptor196.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf196 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0068.pattern196 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0068.pattern196) descriptor196 checked196 (hRep descriptor196.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0068.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0068.regionContext := by
  apply Generated.FunctionalChunk0068.valid
  · exact leaf192 hRep
  · exact leaf193 hRep
  · exact leaf194 hRep
  · exact leaf195 hRep
  · exact leaf196 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0068

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0069
def descriptor197 : OrbitDescriptor := ⟨30, 7, false⟩

theorem checked197 : orbitPatternTransform descriptor197 (Generated.Chunk0069.pattern197) =
    orbitRepresentativePattern descriptor197.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf197 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0069.pattern197 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0069.pattern197) descriptor197 checked197 (hRep descriptor197.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0069.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0069.regionContext := by
  apply Generated.FunctionalChunk0069.valid
  · exact leaf197 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0069

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0070
def descriptor198 : OrbitDescriptor := ⟨45, 7, false⟩

theorem checked198 : orbitPatternTransform descriptor198 (Generated.Chunk0070.pattern198) =
    orbitRepresentativePattern descriptor198.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf198 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0070.pattern198 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0070.pattern198) descriptor198 checked198 (hRep descriptor198.representative)

def descriptor199 : OrbitDescriptor := ⟨46, 7, false⟩

theorem checked199 : orbitPatternTransform descriptor199 (Generated.Chunk0070.pattern199) =
    orbitRepresentativePattern descriptor199.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf199 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0070.pattern199 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0070.pattern199) descriptor199 checked199 (hRep descriptor199.representative)

def descriptor200 : OrbitDescriptor := ⟨47, 7, false⟩

theorem checked200 : orbitPatternTransform descriptor200 (Generated.Chunk0070.pattern200) =
    orbitRepresentativePattern descriptor200.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf200 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0070.pattern200 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0070.pattern200) descriptor200 checked200 (hRep descriptor200.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0070.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0070.regionContext := by
  apply Generated.FunctionalChunk0070.valid
  · exact leaf198 hRep
  · exact leaf199 hRep
  · exact leaf200 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0070

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0071
def descriptor201 : OrbitDescriptor := ⟨58, 7, false⟩

theorem checked201 : orbitPatternTransform descriptor201 (Generated.Chunk0071.pattern201) =
    orbitRepresentativePattern descriptor201.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf201 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0071.pattern201 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0071.pattern201) descriptor201 checked201 (hRep descriptor201.representative)

def descriptor202 : OrbitDescriptor := ⟨59, 7, false⟩

theorem checked202 : orbitPatternTransform descriptor202 (Generated.Chunk0071.pattern202) =
    orbitRepresentativePattern descriptor202.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf202 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0071.pattern202 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0071.pattern202) descriptor202 checked202 (hRep descriptor202.representative)

def descriptor203 : OrbitDescriptor := ⟨60, 7, false⟩

theorem checked203 : orbitPatternTransform descriptor203 (Generated.Chunk0071.pattern203) =
    orbitRepresentativePattern descriptor203.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf203 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0071.pattern203 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0071.pattern203) descriptor203 checked203 (hRep descriptor203.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0071.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0071.regionContext := by
  apply Generated.FunctionalChunk0071.valid
  · exact leaf201 hRep
  · exact leaf202 hRep
  · exact leaf203 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0071
