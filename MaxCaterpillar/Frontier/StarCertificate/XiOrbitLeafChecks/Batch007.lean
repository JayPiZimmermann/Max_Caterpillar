import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0056
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0057
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0058
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0059
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0060
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0061
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0062
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0063
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0056
def descriptor156 : OrbitDescriptor := ⟨29, 7, false⟩

theorem checked156 : orbitPatternTransform descriptor156 (Generated.Chunk0056.pattern156) =
    orbitRepresentativePattern descriptor156.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf156 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0056.pattern156 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0056.pattern156) descriptor156 checked156 (hRep descriptor156.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0056.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0056.regionContext := by
  apply Generated.FunctionalChunk0056.valid
  · exact leaf156 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0056

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0057
def descriptor157 : OrbitDescriptor := ⟨42, 7, false⟩

theorem checked157 : orbitPatternTransform descriptor157 (Generated.Chunk0057.pattern157) =
    orbitRepresentativePattern descriptor157.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf157 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0057.pattern157 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0057.pattern157) descriptor157 checked157 (hRep descriptor157.representative)

def descriptor158 : OrbitDescriptor := ⟨43, 7, false⟩

theorem checked158 : orbitPatternTransform descriptor158 (Generated.Chunk0057.pattern158) =
    orbitRepresentativePattern descriptor158.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf158 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0057.pattern158 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0057.pattern158) descriptor158 checked158 (hRep descriptor158.representative)

def descriptor159 : OrbitDescriptor := ⟨44, 7, false⟩

theorem checked159 : orbitPatternTransform descriptor159 (Generated.Chunk0057.pattern159) =
    orbitRepresentativePattern descriptor159.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf159 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0057.pattern159 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0057.pattern159) descriptor159 checked159 (hRep descriptor159.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0057.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0057.regionContext := by
  apply Generated.FunctionalChunk0057.valid
  · exact leaf157 hRep
  · exact leaf158 hRep
  · exact leaf159 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0057

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0058
def descriptor160 : OrbitDescriptor := ⟨55, 6, false⟩

theorem checked160 : orbitPatternTransform descriptor160 (Generated.Chunk0058.pattern160) =
    orbitRepresentativePattern descriptor160.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf160 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0058.pattern160 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0058.pattern160) descriptor160 checked160 (hRep descriptor160.representative)

def descriptor161 : OrbitDescriptor := ⟨56, 6, false⟩

theorem checked161 : orbitPatternTransform descriptor161 (Generated.Chunk0058.pattern161) =
    orbitRepresentativePattern descriptor161.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf161 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0058.pattern161 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0058.pattern161) descriptor161 checked161 (hRep descriptor161.representative)

def descriptor162 : OrbitDescriptor := ⟨57, 6, false⟩

theorem checked162 : orbitPatternTransform descriptor162 (Generated.Chunk0058.pattern162) =
    orbitRepresentativePattern descriptor162.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf162 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0058.pattern162 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0058.pattern162) descriptor162 checked162 (hRep descriptor162.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0058.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0058.regionContext := by
  apply Generated.FunctionalChunk0058.valid
  · exact leaf160 hRep
  · exact leaf161 hRep
  · exact leaf162 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0058

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0059
def descriptor163 : OrbitDescriptor := ⟨58, 6, false⟩

theorem checked163 : orbitPatternTransform descriptor163 (Generated.Chunk0059.pattern163) =
    orbitRepresentativePattern descriptor163.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf163 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0059.pattern163 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0059.pattern163) descriptor163 checked163 (hRep descriptor163.representative)

def descriptor164 : OrbitDescriptor := ⟨59, 6, false⟩

theorem checked164 : orbitPatternTransform descriptor164 (Generated.Chunk0059.pattern164) =
    orbitRepresentativePattern descriptor164.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf164 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0059.pattern164 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0059.pattern164) descriptor164 checked164 (hRep descriptor164.representative)

def descriptor165 : OrbitDescriptor := ⟨60, 6, false⟩

theorem checked165 : orbitPatternTransform descriptor165 (Generated.Chunk0059.pattern165) =
    orbitRepresentativePattern descriptor165.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf165 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0059.pattern165 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0059.pattern165) descriptor165 checked165 (hRep descriptor165.representative)

def descriptor166 : OrbitDescriptor := ⟨61, 6, false⟩

theorem checked166 : orbitPatternTransform descriptor166 (Generated.Chunk0059.pattern166) =
    orbitRepresentativePattern descriptor166.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf166 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0059.pattern166 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0059.pattern166) descriptor166 checked166 (hRep descriptor166.representative)

def descriptor167 : OrbitDescriptor := ⟨60, 22, true⟩

theorem checked167 : orbitPatternTransform descriptor167 (Generated.Chunk0059.pattern167) =
    orbitRepresentativePattern descriptor167.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf167 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0059.pattern167 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0059.pattern167) descriptor167 checked167 (hRep descriptor167.representative)

def descriptor168 : OrbitDescriptor := ⟨59, 22, true⟩

theorem checked168 : orbitPatternTransform descriptor168 (Generated.Chunk0059.pattern168) =
    orbitRepresentativePattern descriptor168.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf168 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0059.pattern168 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0059.pattern168) descriptor168 checked168 (hRep descriptor168.representative)

def descriptor169 : OrbitDescriptor := ⟨58, 22, true⟩

theorem checked169 : orbitPatternTransform descriptor169 (Generated.Chunk0059.pattern169) =
    orbitRepresentativePattern descriptor169.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf169 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0059.pattern169 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0059.pattern169) descriptor169 checked169 (hRep descriptor169.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0059.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0059.regionContext := by
  apply Generated.FunctionalChunk0059.valid
  · exact leaf163 hRep
  · exact leaf164 hRep
  · exact leaf165 hRep
  · exact leaf166 hRep
  · exact leaf167 hRep
  · exact leaf168 hRep
  · exact leaf169 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0059

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0060
def descriptor170 : OrbitDescriptor := ⟨5, 18, false⟩

theorem checked170 : orbitPatternTransform descriptor170 (Generated.Chunk0060.pattern170) =
    orbitRepresentativePattern descriptor170.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf170 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0060.pattern170 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0060.pattern170) descriptor170 checked170 (hRep descriptor170.representative)

def descriptor171 : OrbitDescriptor := ⟨10, 1, false⟩

theorem checked171 : orbitPatternTransform descriptor171 (Generated.Chunk0060.pattern171) =
    orbitRepresentativePattern descriptor171.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf171 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0060.pattern171 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0060.pattern171) descriptor171 checked171 (hRep descriptor171.representative)

def descriptor172 : OrbitDescriptor := ⟨11, 1, false⟩

theorem checked172 : orbitPatternTransform descriptor172 (Generated.Chunk0060.pattern172) =
    orbitRepresentativePattern descriptor172.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf172 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0060.pattern172 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0060.pattern172) descriptor172 checked172 (hRep descriptor172.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0060.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0060.regionContext := by
  apply Generated.FunctionalChunk0060.valid
  · exact leaf170 hRep
  · exact leaf171 hRep
  · exact leaf172 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0060

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0061
def descriptor173 : OrbitDescriptor := ⟨31, 1, false⟩

theorem checked173 : orbitPatternTransform descriptor173 (Generated.Chunk0061.pattern173) =
    orbitRepresentativePattern descriptor173.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf173 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0061.pattern173 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0061.pattern173) descriptor173 checked173 (hRep descriptor173.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0061.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0061.regionContext := by
  apply Generated.FunctionalChunk0061.valid
  · exact leaf173 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0061

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0062
def descriptor174 : OrbitDescriptor := ⟨48, 1, false⟩

theorem checked174 : orbitPatternTransform descriptor174 (Generated.Chunk0062.pattern174) =
    orbitRepresentativePattern descriptor174.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf174 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0062.pattern174 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0062.pattern174) descriptor174 checked174 (hRep descriptor174.representative)

def descriptor175 : OrbitDescriptor := ⟨62, 0, false⟩

theorem checked175 : orbitPatternTransform descriptor175 (Generated.Chunk0062.pattern175) =
    orbitRepresentativePattern descriptor175.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf175 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0062.pattern175 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0062.pattern175) descriptor175 checked175 (hRep descriptor175.representative)

def descriptor176 : OrbitDescriptor := ⟨57, 22, true⟩

theorem checked176 : orbitPatternTransform descriptor176 (Generated.Chunk0062.pattern176) =
    orbitRepresentativePattern descriptor176.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf176 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0062.pattern176 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0062.pattern176) descriptor176 checked176 (hRep descriptor176.representative)

def descriptor177 : OrbitDescriptor := ⟨56, 22, true⟩

theorem checked177 : orbitPatternTransform descriptor177 (Generated.Chunk0062.pattern177) =
    orbitRepresentativePattern descriptor177.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf177 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0062.pattern177 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0062.pattern177) descriptor177 checked177 (hRep descriptor177.representative)

def descriptor178 : OrbitDescriptor := ⟨55, 22, true⟩

theorem checked178 : orbitPatternTransform descriptor178 (Generated.Chunk0062.pattern178) =
    orbitRepresentativePattern descriptor178.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf178 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0062.pattern178 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0062.pattern178) descriptor178 checked178 (hRep descriptor178.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0062.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0062.regionContext := by
  apply Generated.FunctionalChunk0062.valid
  · exact leaf174 hRep
  · exact leaf175 hRep
  · exact leaf176 hRep
  · exact leaf177 hRep
  · exact leaf178 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0062

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0063
def descriptor179 : OrbitDescriptor := ⟨6, 18, false⟩

theorem checked179 : orbitPatternTransform descriptor179 (Generated.Chunk0063.pattern179) =
    orbitRepresentativePattern descriptor179.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf179 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0063.pattern179 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0063.pattern179) descriptor179 checked179 (hRep descriptor179.representative)

def descriptor180 : OrbitDescriptor := ⟨11, 4, false⟩

theorem checked180 : orbitPatternTransform descriptor180 (Generated.Chunk0063.pattern180) =
    orbitRepresentativePattern descriptor180.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf180 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0063.pattern180 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0063.pattern180) descriptor180 checked180 (hRep descriptor180.representative)

def descriptor181 : OrbitDescriptor := ⟨12, 1, false⟩

theorem checked181 : orbitPatternTransform descriptor181 (Generated.Chunk0063.pattern181) =
    orbitRepresentativePattern descriptor181.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf181 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0063.pattern181 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0063.pattern181) descriptor181 checked181 (hRep descriptor181.representative)

def descriptor182 : OrbitDescriptor := ⟨13, 1, false⟩

theorem checked182 : orbitPatternTransform descriptor182 (Generated.Chunk0063.pattern182) =
    orbitRepresentativePattern descriptor182.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf182 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0063.pattern182 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0063.pattern182) descriptor182 checked182 (hRep descriptor182.representative)

def descriptor183 : OrbitDescriptor := ⟨14, 1, false⟩

theorem checked183 : orbitPatternTransform descriptor183 (Generated.Chunk0063.pattern183) =
    orbitRepresentativePattern descriptor183.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf183 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0063.pattern183 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0063.pattern183) descriptor183 checked183 (hRep descriptor183.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0063.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0063.regionContext := by
  apply Generated.FunctionalChunk0063.valid
  · exact leaf179 hRep
  · exact leaf180 hRep
  · exact leaf181 hRep
  · exact leaf182 hRep
  · exact leaf183 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0063
