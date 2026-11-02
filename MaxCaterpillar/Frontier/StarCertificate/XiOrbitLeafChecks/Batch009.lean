import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0072
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0073
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0074
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0075
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0076
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0077
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0078
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0079
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0072
def descriptor204 : OrbitDescriptor := ⟨54, 16, true⟩

theorem checked204 : orbitPatternTransform descriptor204 (Generated.Chunk0072.pattern204) =
    orbitRepresentativePattern descriptor204.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf204 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0072.pattern204 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0072.pattern204) descriptor204 checked204 (hRep descriptor204.representative)

def descriptor205 : OrbitDescriptor := ⟨53, 16, true⟩

theorem checked205 : orbitPatternTransform descriptor205 (Generated.Chunk0072.pattern205) =
    orbitRepresentativePattern descriptor205.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf205 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0072.pattern205 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0072.pattern205) descriptor205 checked205 (hRep descriptor205.representative)

def descriptor206 : OrbitDescriptor := ⟨52, 16, true⟩

theorem checked206 : orbitPatternTransform descriptor206 (Generated.Chunk0072.pattern206) =
    orbitRepresentativePattern descriptor206.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf206 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0072.pattern206 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0072.pattern206) descriptor206 checked206 (hRep descriptor206.representative)

def descriptor207 : OrbitDescriptor := ⟨51, 16, true⟩

theorem checked207 : orbitPatternTransform descriptor207 (Generated.Chunk0072.pattern207) =
    orbitRepresentativePattern descriptor207.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf207 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0072.pattern207 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0072.pattern207) descriptor207 checked207 (hRep descriptor207.representative)

def descriptor208 : OrbitDescriptor := ⟨50, 16, true⟩

theorem checked208 : orbitPatternTransform descriptor208 (Generated.Chunk0072.pattern208) =
    orbitRepresentativePattern descriptor208.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf208 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0072.pattern208 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0072.pattern208) descriptor208 checked208 (hRep descriptor208.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0072.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0072.regionContext := by
  apply Generated.FunctionalChunk0072.valid
  · exact leaf204 hRep
  · exact leaf205 hRep
  · exact leaf206 hRep
  · exact leaf207 hRep
  · exact leaf208 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0072

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0073
def descriptor209 : OrbitDescriptor := ⟨49, 22, true⟩

theorem checked209 : orbitPatternTransform descriptor209 (Generated.Chunk0073.pattern209) =
    orbitRepresentativePattern descriptor209.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf209 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0073.pattern209 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0073.pattern209) descriptor209 checked209 (hRep descriptor209.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0073.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0073.regionContext := by
  apply Generated.FunctionalChunk0073.valid
  · exact leaf209 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0073

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0074
def descriptor210 : OrbitDescriptor := ⟨47, 22, true⟩

theorem checked210 : orbitPatternTransform descriptor210 (Generated.Chunk0074.pattern210) =
    orbitRepresentativePattern descriptor210.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf210 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0074.pattern210 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0074.pattern210) descriptor210 checked210 (hRep descriptor210.representative)

def descriptor211 : OrbitDescriptor := ⟨46, 22, true⟩

theorem checked211 : orbitPatternTransform descriptor211 (Generated.Chunk0074.pattern211) =
    orbitRepresentativePattern descriptor211.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf211 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0074.pattern211 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0074.pattern211) descriptor211 checked211 (hRep descriptor211.representative)

def descriptor212 : OrbitDescriptor := ⟨45, 22, true⟩

theorem checked212 : orbitPatternTransform descriptor212 (Generated.Chunk0074.pattern212) =
    orbitRepresentativePattern descriptor212.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf212 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0074.pattern212 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0074.pattern212) descriptor212 checked212 (hRep descriptor212.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0074.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0074.regionContext := by
  apply Generated.FunctionalChunk0074.valid
  · exact leaf210 hRep
  · exact leaf211 hRep
  · exact leaf212 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0074

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0075
def descriptor213 : OrbitDescriptor := ⟨6, 20, false⟩

theorem checked213 : orbitPatternTransform descriptor213 (Generated.Chunk0075.pattern213) =
    orbitRepresentativePattern descriptor213.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf213 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0075.pattern213 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0075.pattern213) descriptor213 checked213 (hRep descriptor213.representative)

def descriptor214 : OrbitDescriptor := ⟨11, 10, false⟩

theorem checked214 : orbitPatternTransform descriptor214 (Generated.Chunk0075.pattern214) =
    orbitRepresentativePattern descriptor214.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf214 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0075.pattern214 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0075.pattern214) descriptor214 checked214 (hRep descriptor214.representative)

def descriptor215 : OrbitDescriptor := ⟨12, 7, false⟩

theorem checked215 : orbitPatternTransform descriptor215 (Generated.Chunk0075.pattern215) =
    orbitRepresentativePattern descriptor215.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf215 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0075.pattern215 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0075.pattern215) descriptor215 checked215 (hRep descriptor215.representative)

def descriptor216 : OrbitDescriptor := ⟨13, 7, false⟩

theorem checked216 : orbitPatternTransform descriptor216 (Generated.Chunk0075.pattern216) =
    orbitRepresentativePattern descriptor216.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf216 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0075.pattern216 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0075.pattern216) descriptor216 checked216 (hRep descriptor216.representative)

def descriptor217 : OrbitDescriptor := ⟨14, 7, false⟩

theorem checked217 : orbitPatternTransform descriptor217 (Generated.Chunk0075.pattern217) =
    orbitRepresentativePattern descriptor217.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf217 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0075.pattern217 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0075.pattern217) descriptor217 checked217 (hRep descriptor217.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0075.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0075.regionContext := by
  apply Generated.FunctionalChunk0075.valid
  · exact leaf213 hRep
  · exact leaf214 hRep
  · exact leaf215 hRep
  · exact leaf216 hRep
  · exact leaf217 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0075

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0076
def descriptor218 : OrbitDescriptor := ⟨32, 7, false⟩

theorem checked218 : orbitPatternTransform descriptor218 (Generated.Chunk0076.pattern218) =
    orbitRepresentativePattern descriptor218.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf218 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0076.pattern218 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0076.pattern218) descriptor218 checked218 (hRep descriptor218.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0076.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0076.regionContext := by
  apply Generated.FunctionalChunk0076.valid
  · exact leaf218 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0076

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0077
def descriptor219 : OrbitDescriptor := ⟨49, 7, false⟩

theorem checked219 : orbitPatternTransform descriptor219 (Generated.Chunk0077.pattern219) =
    orbitRepresentativePattern descriptor219.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf219 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0077.pattern219 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0077.pattern219) descriptor219 checked219 (hRep descriptor219.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0077.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0077.regionContext := by
  apply Generated.FunctionalChunk0077.valid
  · exact leaf219 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0077

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0078
def descriptor220 : OrbitDescriptor := ⟨61, 7, false⟩

theorem checked220 : orbitPatternTransform descriptor220 (Generated.Chunk0078.pattern220) =
    orbitRepresentativePattern descriptor220.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf220 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0078.pattern220 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0078.pattern220) descriptor220 checked220 (hRep descriptor220.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0078.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0078.regionContext := by
  apply Generated.FunctionalChunk0078.valid
  · exact leaf220 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0078

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0079
def descriptor221 : OrbitDescriptor := ⟨49, 16, true⟩

theorem checked221 : orbitPatternTransform descriptor221 (Generated.Chunk0079.pattern221) =
    orbitRepresentativePattern descriptor221.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf221 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0079.pattern221 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0079.pattern221) descriptor221 checked221 (hRep descriptor221.representative)

def descriptor222 : OrbitDescriptor := ⟨48, 16, true⟩

theorem checked222 : orbitPatternTransform descriptor222 (Generated.Chunk0079.pattern222) =
    orbitRepresentativePattern descriptor222.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf222 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0079.pattern222 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0079.pattern222) descriptor222 checked222 (hRep descriptor222.representative)

def descriptor223 : OrbitDescriptor := ⟨44, 22, true⟩

theorem checked223 : orbitPatternTransform descriptor223 (Generated.Chunk0079.pattern223) =
    orbitRepresentativePattern descriptor223.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf223 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0079.pattern223 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0079.pattern223) descriptor223 checked223 (hRep descriptor223.representative)

def descriptor224 : OrbitDescriptor := ⟨43, 22, true⟩

theorem checked224 : orbitPatternTransform descriptor224 (Generated.Chunk0079.pattern224) =
    orbitRepresentativePattern descriptor224.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf224 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0079.pattern224 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0079.pattern224) descriptor224 checked224 (hRep descriptor224.representative)

def descriptor225 : OrbitDescriptor := ⟨42, 22, true⟩

theorem checked225 : orbitPatternTransform descriptor225 (Generated.Chunk0079.pattern225) =
    orbitRepresentativePattern descriptor225.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf225 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0079.pattern225 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0079.pattern225) descriptor225 checked225 (hRep descriptor225.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0079.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0079.regionContext := by
  apply Generated.FunctionalChunk0079.valid
  · exact leaf221 hRep
  · exact leaf222 hRep
  · exact leaf223 hRep
  · exact leaf224 hRep
  · exact leaf225 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0079
