import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0200
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0201
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0202
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0203
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0204
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0205
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0206
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0207
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0200
def descriptor572 : OrbitDescriptor := ⟨32, 11, true⟩

theorem checked572 : orbitPatternTransform descriptor572 (Generated.Chunk0200.pattern572) =
    orbitRepresentativePattern descriptor572.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf572 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0200.pattern572 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0200.pattern572) descriptor572 checked572 (hRep descriptor572.representative)

def descriptor573 : OrbitDescriptor := ⟨31, 11, true⟩

theorem checked573 : orbitPatternTransform descriptor573 (Generated.Chunk0200.pattern573) =
    orbitRepresentativePattern descriptor573.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf573 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0200.pattern573 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0200.pattern573) descriptor573 checked573 (hRep descriptor573.representative)

def descriptor574 : OrbitDescriptor := ⟨29, 21, true⟩

theorem checked574 : orbitPatternTransform descriptor574 (Generated.Chunk0200.pattern574) =
    orbitRepresentativePattern descriptor574.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf574 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0200.pattern574 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0200.pattern574) descriptor574 checked574 (hRep descriptor574.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0200.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0200.regionContext := by
  apply Generated.FunctionalChunk0200.valid
  · exact leaf572 hRep
  · exact leaf573 hRep
  · exact leaf574 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0200

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0201
def descriptor575 : OrbitDescriptor := ⟨42, 19, false⟩

theorem checked575 : orbitPatternTransform descriptor575 (Generated.Chunk0201.pattern575) =
    orbitRepresentativePattern descriptor575.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf575 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0201.pattern575 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0201.pattern575) descriptor575 checked575 (hRep descriptor575.representative)

def descriptor576 : OrbitDescriptor := ⟨43, 19, false⟩

theorem checked576 : orbitPatternTransform descriptor576 (Generated.Chunk0201.pattern576) =
    orbitRepresentativePattern descriptor576.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf576 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0201.pattern576 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0201.pattern576) descriptor576 checked576 (hRep descriptor576.representative)

def descriptor577 : OrbitDescriptor := ⟨44, 19, false⟩

theorem checked577 : orbitPatternTransform descriptor577 (Generated.Chunk0201.pattern577) =
    orbitRepresentativePattern descriptor577.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf577 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0201.pattern577 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0201.pattern577) descriptor577 checked577 (hRep descriptor577.representative)

def descriptor578 : OrbitDescriptor := ⟨48, 5, false⟩

theorem checked578 : orbitPatternTransform descriptor578 (Generated.Chunk0201.pattern578) =
    orbitRepresentativePattern descriptor578.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf578 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0201.pattern578 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0201.pattern578) descriptor578 checked578 (hRep descriptor578.representative)

def descriptor579 : OrbitDescriptor := ⟨49, 5, false⟩

theorem checked579 : orbitPatternTransform descriptor579 (Generated.Chunk0201.pattern579) =
    orbitRepresentativePattern descriptor579.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf579 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0201.pattern579 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0201.pattern579) descriptor579 checked579 (hRep descriptor579.representative)

def descriptor580 : OrbitDescriptor := ⟨61, 5, false⟩

theorem checked580 : orbitPatternTransform descriptor580 (Generated.Chunk0201.pattern580) =
    orbitRepresentativePattern descriptor580.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf580 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0201.pattern580 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0201.pattern580) descriptor580 checked580 (hRep descriptor580.representative)

def descriptor581 : OrbitDescriptor := ⟨49, 9, true⟩

theorem checked581 : orbitPatternTransform descriptor581 (Generated.Chunk0201.pattern581) =
    orbitRepresentativePattern descriptor581.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf581 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0201.pattern581 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0201.pattern581) descriptor581 checked581 (hRep descriptor581.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0201.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0201.regionContext := by
  apply Generated.FunctionalChunk0201.valid
  · exact leaf575 hRep
  · exact leaf576 hRep
  · exact leaf577 hRep
  · exact leaf578 hRep
  · exact leaf579 hRep
  · exact leaf580 hRep
  · exact leaf581 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0201

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0202
def descriptor582 : OrbitDescriptor := ⟨32, 9, true⟩

theorem checked582 : orbitPatternTransform descriptor582 (Generated.Chunk0202.pattern582) =
    orbitRepresentativePattern descriptor582.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf582 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0202.pattern582 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0202.pattern582) descriptor582 checked582 (hRep descriptor582.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0202.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0202.regionContext := by
  apply Generated.FunctionalChunk0202.valid
  · exact leaf582 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0202

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0203
def descriptor583 : OrbitDescriptor := ⟨14, 9, true⟩

theorem checked583 : orbitPatternTransform descriptor583 (Generated.Chunk0203.pattern583) =
    orbitRepresentativePattern descriptor583.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf583 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0203.pattern583 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0203.pattern583) descriptor583 checked583 (hRep descriptor583.representative)

def descriptor584 : OrbitDescriptor := ⟨13, 9, true⟩

theorem checked584 : orbitPatternTransform descriptor584 (Generated.Chunk0203.pattern584) =
    orbitRepresentativePattern descriptor584.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf584 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0203.pattern584 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0203.pattern584) descriptor584 checked584 (hRep descriptor584.representative)

def descriptor585 : OrbitDescriptor := ⟨12, 9, true⟩

theorem checked585 : orbitPatternTransform descriptor585 (Generated.Chunk0203.pattern585) =
    orbitRepresentativePattern descriptor585.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf585 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0203.pattern585 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0203.pattern585) descriptor585 checked585 (hRep descriptor585.representative)

def descriptor586 : OrbitDescriptor := ⟨11, 11, true⟩

theorem checked586 : orbitPatternTransform descriptor586 (Generated.Chunk0203.pattern586) =
    orbitRepresentativePattern descriptor586.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf586 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0203.pattern586 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0203.pattern586) descriptor586 checked586 (hRep descriptor586.representative)

def descriptor587 : OrbitDescriptor := ⟨6, 21, true⟩

theorem checked587 : orbitPatternTransform descriptor587 (Generated.Chunk0203.pattern587) =
    orbitRepresentativePattern descriptor587.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf587 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0203.pattern587 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0203.pattern587) descriptor587 checked587 (hRep descriptor587.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0203.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0203.regionContext := by
  apply Generated.FunctionalChunk0203.valid
  · exact leaf583 hRep
  · exact leaf584 hRep
  · exact leaf585 hRep
  · exact leaf586 hRep
  · exact leaf587 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0203

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0204
def descriptor588 : OrbitDescriptor := ⟨55, 18, false⟩

theorem checked588 : orbitPatternTransform descriptor588 (Generated.Chunk0204.pattern588) =
    orbitRepresentativePattern descriptor588.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf588 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0204.pattern588 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0204.pattern588) descriptor588 checked588 (hRep descriptor588.representative)

def descriptor589 : OrbitDescriptor := ⟨56, 18, false⟩

theorem checked589 : orbitPatternTransform descriptor589 (Generated.Chunk0204.pattern589) =
    orbitRepresentativePattern descriptor589.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf589 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0204.pattern589 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0204.pattern589) descriptor589 checked589 (hRep descriptor589.representative)

def descriptor590 : OrbitDescriptor := ⟨57, 18, false⟩

theorem checked590 : orbitPatternTransform descriptor590 (Generated.Chunk0204.pattern590) =
    orbitRepresentativePattern descriptor590.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf590 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0204.pattern590 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0204.pattern590) descriptor590 checked590 (hRep descriptor590.representative)

def descriptor591 : OrbitDescriptor := ⟨62, 4, false⟩

theorem checked591 : orbitPatternTransform descriptor591 (Generated.Chunk0204.pattern591) =
    orbitRepresentativePattern descriptor591.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf591 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0204.pattern591 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0204.pattern591) descriptor591 checked591 (hRep descriptor591.representative)

def descriptor592 : OrbitDescriptor := ⟨48, 9, true⟩

theorem checked592 : orbitPatternTransform descriptor592 (Generated.Chunk0204.pattern592) =
    orbitRepresentativePattern descriptor592.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf592 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0204.pattern592 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0204.pattern592) descriptor592 checked592 (hRep descriptor592.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0204.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0204.regionContext := by
  apply Generated.FunctionalChunk0204.valid
  · exact leaf588 hRep
  · exact leaf589 hRep
  · exact leaf590 hRep
  · exact leaf591 hRep
  · exact leaf592 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0204

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0205
def descriptor593 : OrbitDescriptor := ⟨31, 9, true⟩

theorem checked593 : orbitPatternTransform descriptor593 (Generated.Chunk0205.pattern593) =
    orbitRepresentativePattern descriptor593.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf593 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0205.pattern593 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0205.pattern593) descriptor593 checked593 (hRep descriptor593.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0205.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0205.regionContext := by
  apply Generated.FunctionalChunk0205.valid
  · exact leaf593 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0205

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0206
def descriptor594 : OrbitDescriptor := ⟨11, 9, true⟩

theorem checked594 : orbitPatternTransform descriptor594 (Generated.Chunk0206.pattern594) =
    orbitRepresentativePattern descriptor594.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf594 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0206.pattern594 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0206.pattern594) descriptor594 checked594 (hRep descriptor594.representative)

def descriptor595 : OrbitDescriptor := ⟨10, 9, true⟩

theorem checked595 : orbitPatternTransform descriptor595 (Generated.Chunk0206.pattern595) =
    orbitRepresentativePattern descriptor595.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf595 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0206.pattern595 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0206.pattern595) descriptor595 checked595 (hRep descriptor595.representative)

def descriptor596 : OrbitDescriptor := ⟨5, 21, true⟩

theorem checked596 : orbitPatternTransform descriptor596 (Generated.Chunk0206.pattern596) =
    orbitRepresentativePattern descriptor596.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf596 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0206.pattern596 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0206.pattern596) descriptor596 checked596 (hRep descriptor596.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0206.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0206.regionContext := by
  apply Generated.FunctionalChunk0206.valid
  · exact leaf594 hRep
  · exact leaf595 hRep
  · exact leaf596 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0206

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0207
def descriptor597 : OrbitDescriptor := ⟨58, 18, false⟩

theorem checked597 : orbitPatternTransform descriptor597 (Generated.Chunk0207.pattern597) =
    orbitRepresentativePattern descriptor597.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf597 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0207.pattern597 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0207.pattern597) descriptor597 checked597 (hRep descriptor597.representative)

def descriptor598 : OrbitDescriptor := ⟨59, 18, false⟩

theorem checked598 : orbitPatternTransform descriptor598 (Generated.Chunk0207.pattern598) =
    orbitRepresentativePattern descriptor598.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf598 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0207.pattern598 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0207.pattern598) descriptor598 checked598 (hRep descriptor598.representative)

def descriptor599 : OrbitDescriptor := ⟨60, 18, false⟩

theorem checked599 : orbitPatternTransform descriptor599 (Generated.Chunk0207.pattern599) =
    orbitRepresentativePattern descriptor599.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf599 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0207.pattern599 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0207.pattern599) descriptor599 checked599 (hRep descriptor599.representative)

def descriptor600 : OrbitDescriptor := ⟨61, 18, false⟩

theorem checked600 : orbitPatternTransform descriptor600 (Generated.Chunk0207.pattern600) =
    orbitRepresentativePattern descriptor600.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf600 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0207.pattern600 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0207.pattern600) descriptor600 checked600 (hRep descriptor600.representative)

def descriptor601 : OrbitDescriptor := ⟨60, 14, true⟩

theorem checked601 : orbitPatternTransform descriptor601 (Generated.Chunk0207.pattern601) =
    orbitRepresentativePattern descriptor601.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf601 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0207.pattern601 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0207.pattern601) descriptor601 checked601 (hRep descriptor601.representative)

def descriptor602 : OrbitDescriptor := ⟨59, 14, true⟩

theorem checked602 : orbitPatternTransform descriptor602 (Generated.Chunk0207.pattern602) =
    orbitRepresentativePattern descriptor602.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf602 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0207.pattern602 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0207.pattern602) descriptor602 checked602 (hRep descriptor602.representative)

def descriptor603 : OrbitDescriptor := ⟨58, 14, true⟩

theorem checked603 : orbitPatternTransform descriptor603 (Generated.Chunk0207.pattern603) =
    orbitRepresentativePattern descriptor603.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf603 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0207.pattern603 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0207.pattern603) descriptor603 checked603 (hRep descriptor603.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0207.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0207.regionContext := by
  apply Generated.FunctionalChunk0207.valid
  · exact leaf597 hRep
  · exact leaf598 hRep
  · exact leaf599 hRep
  · exact leaf600 hRep
  · exact leaf601 hRep
  · exact leaf602 hRep
  · exact leaf603 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0207
