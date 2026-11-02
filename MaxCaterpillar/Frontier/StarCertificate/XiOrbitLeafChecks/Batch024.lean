import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0192
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0193
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0194
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0195
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0196
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0197
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0198
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0199
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0192
def descriptor546 : OrbitDescriptor := ⟨5, 19, false⟩

theorem checked546 : orbitPatternTransform descriptor546 (Generated.Chunk0192.pattern546) =
    orbitRepresentativePattern descriptor546.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf546 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0192.pattern546 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0192.pattern546) descriptor546 checked546 (hRep descriptor546.representative)

def descriptor547 : OrbitDescriptor := ⟨10, 3, false⟩

theorem checked547 : orbitPatternTransform descriptor547 (Generated.Chunk0192.pattern547) =
    orbitRepresentativePattern descriptor547.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf547 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0192.pattern547 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0192.pattern547) descriptor547 checked547 (hRep descriptor547.representative)

def descriptor548 : OrbitDescriptor := ⟨11, 3, false⟩

theorem checked548 : orbitPatternTransform descriptor548 (Generated.Chunk0192.pattern548) =
    orbitRepresentativePattern descriptor548.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf548 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0192.pattern548 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0192.pattern548) descriptor548 checked548 (hRep descriptor548.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0192.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0192.regionContext := by
  apply Generated.FunctionalChunk0192.valid
  · exact leaf546 hRep
  · exact leaf547 hRep
  · exact leaf548 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0192

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0193
def descriptor549 : OrbitDescriptor := ⟨31, 3, false⟩

theorem checked549 : orbitPatternTransform descriptor549 (Generated.Chunk0193.pattern549) =
    orbitRepresentativePattern descriptor549.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf549 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0193.pattern549 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0193.pattern549) descriptor549 checked549 (hRep descriptor549.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0193.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0193.regionContext := by
  apply Generated.FunctionalChunk0193.valid
  · exact leaf549 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0193

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0194
def descriptor550 : OrbitDescriptor := ⟨48, 3, false⟩

theorem checked550 : orbitPatternTransform descriptor550 (Generated.Chunk0194.pattern550) =
    orbitRepresentativePattern descriptor550.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf550 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0194.pattern550 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0194.pattern550) descriptor550 checked550 (hRep descriptor550.representative)

def descriptor551 : OrbitDescriptor := ⟨62, 2, false⟩

theorem checked551 : orbitPatternTransform descriptor551 (Generated.Chunk0194.pattern551) =
    orbitRepresentativePattern descriptor551.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf551 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0194.pattern551 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0194.pattern551) descriptor551 checked551 (hRep descriptor551.representative)

def descriptor552 : OrbitDescriptor := ⟨57, 20, true⟩

theorem checked552 : orbitPatternTransform descriptor552 (Generated.Chunk0194.pattern552) =
    orbitRepresentativePattern descriptor552.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf552 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0194.pattern552 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0194.pattern552) descriptor552 checked552 (hRep descriptor552.representative)

def descriptor553 : OrbitDescriptor := ⟨56, 20, true⟩

theorem checked553 : orbitPatternTransform descriptor553 (Generated.Chunk0194.pattern553) =
    orbitRepresentativePattern descriptor553.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf553 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0194.pattern553 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0194.pattern553) descriptor553 checked553 (hRep descriptor553.representative)

def descriptor554 : OrbitDescriptor := ⟨55, 20, true⟩

theorem checked554 : orbitPatternTransform descriptor554 (Generated.Chunk0194.pattern554) =
    orbitRepresentativePattern descriptor554.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf554 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0194.pattern554 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0194.pattern554) descriptor554 checked554 (hRep descriptor554.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0194.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0194.regionContext := by
  apply Generated.FunctionalChunk0194.valid
  · exact leaf550 hRep
  · exact leaf551 hRep
  · exact leaf552 hRep
  · exact leaf553 hRep
  · exact leaf554 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0194

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0195
def descriptor555 : OrbitDescriptor := ⟨6, 19, false⟩

theorem checked555 : orbitPatternTransform descriptor555 (Generated.Chunk0195.pattern555) =
    orbitRepresentativePattern descriptor555.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf555 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0195.pattern555 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0195.pattern555) descriptor555 checked555 (hRep descriptor555.representative)

def descriptor556 : OrbitDescriptor := ⟨11, 5, false⟩

theorem checked556 : orbitPatternTransform descriptor556 (Generated.Chunk0195.pattern556) =
    orbitRepresentativePattern descriptor556.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf556 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0195.pattern556 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0195.pattern556) descriptor556 checked556 (hRep descriptor556.representative)

def descriptor557 : OrbitDescriptor := ⟨12, 3, false⟩

theorem checked557 : orbitPatternTransform descriptor557 (Generated.Chunk0195.pattern557) =
    orbitRepresentativePattern descriptor557.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf557 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0195.pattern557 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0195.pattern557) descriptor557 checked557 (hRep descriptor557.representative)

def descriptor558 : OrbitDescriptor := ⟨13, 3, false⟩

theorem checked558 : orbitPatternTransform descriptor558 (Generated.Chunk0195.pattern558) =
    orbitRepresentativePattern descriptor558.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf558 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0195.pattern558 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0195.pattern558) descriptor558 checked558 (hRep descriptor558.representative)

def descriptor559 : OrbitDescriptor := ⟨14, 3, false⟩

theorem checked559 : orbitPatternTransform descriptor559 (Generated.Chunk0195.pattern559) =
    orbitRepresentativePattern descriptor559.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf559 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0195.pattern559 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0195.pattern559) descriptor559 checked559 (hRep descriptor559.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0195.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0195.regionContext := by
  apply Generated.FunctionalChunk0195.valid
  · exact leaf555 hRep
  · exact leaf556 hRep
  · exact leaf557 hRep
  · exact leaf558 hRep
  · exact leaf559 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0195

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0196
def descriptor560 : OrbitDescriptor := ⟨32, 3, false⟩

theorem checked560 : orbitPatternTransform descriptor560 (Generated.Chunk0196.pattern560) =
    orbitRepresentativePattern descriptor560.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf560 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0196.pattern560 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0196.pattern560) descriptor560 checked560 (hRep descriptor560.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0196.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0196.regionContext := by
  apply Generated.FunctionalChunk0196.valid
  · exact leaf560 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0196

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0197
def descriptor561 : OrbitDescriptor := ⟨49, 3, false⟩

theorem checked561 : orbitPatternTransform descriptor561 (Generated.Chunk0197.pattern561) =
    orbitRepresentativePattern descriptor561.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf561 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0197.pattern561 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0197.pattern561) descriptor561 checked561 (hRep descriptor561.representative)

def descriptor562 : OrbitDescriptor := ⟨61, 3, false⟩

theorem checked562 : orbitPatternTransform descriptor562 (Generated.Chunk0197.pattern562) =
    orbitRepresentativePattern descriptor562.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf562 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0197.pattern562 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0197.pattern562) descriptor562 checked562 (hRep descriptor562.representative)

def descriptor563 : OrbitDescriptor := ⟨49, 11, true⟩

theorem checked563 : orbitPatternTransform descriptor563 (Generated.Chunk0197.pattern563) =
    orbitRepresentativePattern descriptor563.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf563 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0197.pattern563 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0197.pattern563) descriptor563 checked563 (hRep descriptor563.representative)

def descriptor564 : OrbitDescriptor := ⟨48, 11, true⟩

theorem checked564 : orbitPatternTransform descriptor564 (Generated.Chunk0197.pattern564) =
    orbitRepresentativePattern descriptor564.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf564 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0197.pattern564 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0197.pattern564) descriptor564 checked564 (hRep descriptor564.representative)

def descriptor565 : OrbitDescriptor := ⟨44, 21, true⟩

theorem checked565 : orbitPatternTransform descriptor565 (Generated.Chunk0197.pattern565) =
    orbitRepresentativePattern descriptor565.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf565 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0197.pattern565 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0197.pattern565) descriptor565 checked565 (hRep descriptor565.representative)

def descriptor566 : OrbitDescriptor := ⟨43, 21, true⟩

theorem checked566 : orbitPatternTransform descriptor566 (Generated.Chunk0197.pattern566) =
    orbitRepresentativePattern descriptor566.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf566 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0197.pattern566 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0197.pattern566) descriptor566 checked566 (hRep descriptor566.representative)

def descriptor567 : OrbitDescriptor := ⟨42, 21, true⟩

theorem checked567 : orbitPatternTransform descriptor567 (Generated.Chunk0197.pattern567) =
    orbitRepresentativePattern descriptor567.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf567 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0197.pattern567 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0197.pattern567) descriptor567 checked567 (hRep descriptor567.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0197.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0197.regionContext := by
  apply Generated.FunctionalChunk0197.valid
  · exact leaf561 hRep
  · exact leaf562 hRep
  · exact leaf563 hRep
  · exact leaf564 hRep
  · exact leaf565 hRep
  · exact leaf566 hRep
  · exact leaf567 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0197

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0198
def descriptor568 : OrbitDescriptor := ⟨29, 19, false⟩

theorem checked568 : orbitPatternTransform descriptor568 (Generated.Chunk0198.pattern568) =
    orbitRepresentativePattern descriptor568.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf568 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0198.pattern568 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0198.pattern568) descriptor568 checked568 (hRep descriptor568.representative)

def descriptor569 : OrbitDescriptor := ⟨31, 5, false⟩

theorem checked569 : orbitPatternTransform descriptor569 (Generated.Chunk0198.pattern569) =
    orbitRepresentativePattern descriptor569.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf569 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0198.pattern569 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0198.pattern569) descriptor569 checked569 (hRep descriptor569.representative)

def descriptor570 : OrbitDescriptor := ⟨32, 5, false⟩

theorem checked570 : orbitPatternTransform descriptor570 (Generated.Chunk0198.pattern570) =
    orbitRepresentativePattern descriptor570.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf570 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0198.pattern570 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0198.pattern570) descriptor570 checked570 (hRep descriptor570.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0198.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0198.regionContext := by
  apply Generated.FunctionalChunk0198.valid
  · exact leaf568 hRep
  · exact leaf569 hRep
  · exact leaf570 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0198

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0199
def descriptor571 : OrbitDescriptor := ⟨65, 3, false⟩

theorem checked571 : orbitPatternTransform descriptor571 (Generated.Chunk0199.pattern571) =
    orbitRepresentativePattern descriptor571.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf571 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0199.pattern571 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0199.pattern571) descriptor571 checked571 (hRep descriptor571.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0199.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0199.regionContext := by
  apply Generated.FunctionalChunk0199.valid
  · exact leaf571 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0199
