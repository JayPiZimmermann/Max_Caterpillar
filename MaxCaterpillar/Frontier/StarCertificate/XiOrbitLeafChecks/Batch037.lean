import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0296
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0297
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0298
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0299
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0300
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0301
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0302
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0303
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0296
def descriptor860 : OrbitDescriptor := ⟨64, 13, false⟩

theorem checked860 : orbitPatternTransform descriptor860 (Generated.Chunk0296.pattern860) =
    orbitRepresentativePattern descriptor860.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf860 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0296.pattern860 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0296.pattern860) descriptor860 checked860 (hRep descriptor860.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0296.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0296.regionContext := by
  apply Generated.FunctionalChunk0296.valid
  · exact leaf860 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0296

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0297
def descriptor861 : OrbitDescriptor := ⟨35, 10, true⟩

theorem checked861 : orbitPatternTransform descriptor861 (Generated.Chunk0297.pattern861) =
    orbitRepresentativePattern descriptor861.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf861 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0297.pattern861 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0297.pattern861) descriptor861 checked861 (hRep descriptor861.representative)

def descriptor862 : OrbitDescriptor := ⟨34, 10, true⟩

theorem checked862 : orbitPatternTransform descriptor862 (Generated.Chunk0297.pattern862) =
    orbitRepresentativePattern descriptor862.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf862 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0297.pattern862 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0297.pattern862) descriptor862 checked862 (hRep descriptor862.representative)

def descriptor863 : OrbitDescriptor := ⟨33, 10, true⟩

theorem checked863 : orbitPatternTransform descriptor863 (Generated.Chunk0297.pattern863) =
    orbitRepresentativePattern descriptor863.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf863 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0297.pattern863 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0297.pattern863) descriptor863 checked863 (hRep descriptor863.representative)

def descriptor864 : OrbitDescriptor := ⟨32, 20, true⟩

theorem checked864 : orbitPatternTransform descriptor864 (Generated.Chunk0297.pattern864) =
    orbitRepresentativePattern descriptor864.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf864 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0297.pattern864 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0297.pattern864) descriptor864 checked864 (hRep descriptor864.representative)

def descriptor865 : OrbitDescriptor := ⟨30, 20, true⟩

theorem checked865 : orbitPatternTransform descriptor865 (Generated.Chunk0297.pattern865) =
    orbitRepresentativePattern descriptor865.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf865 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0297.pattern865 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0297.pattern865) descriptor865 checked865 (hRep descriptor865.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0297.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0297.regionContext := by
  apply Generated.FunctionalChunk0297.valid
  · exact leaf861 hRep
  · exact leaf862 hRep
  · exact leaf863 hRep
  · exact leaf864 hRep
  · exact leaf865 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0297

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0298
def descriptor866 : OrbitDescriptor := ⟨29, 22, false⟩

theorem checked866 : orbitPatternTransform descriptor866 (Generated.Chunk0298.pattern866) =
    orbitRepresentativePattern descriptor866.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf866 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0298.pattern866 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0298.pattern866) descriptor866 checked866 (hRep descriptor866.representative)

def descriptor867 : OrbitDescriptor := ⟨31, 16, false⟩

theorem checked867 : orbitPatternTransform descriptor867 (Generated.Chunk0298.pattern867) =
    orbitRepresentativePattern descriptor867.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf867 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0298.pattern867 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0298.pattern867) descriptor867 checked867 (hRep descriptor867.representative)

def descriptor868 : OrbitDescriptor := ⟨32, 16, false⟩

theorem checked868 : orbitPatternTransform descriptor868 (Generated.Chunk0298.pattern868) =
    orbitRepresentativePattern descriptor868.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf868 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0298.pattern868 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0298.pattern868) descriptor868 checked868 (hRep descriptor868.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0298.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0298.regionContext := by
  apply Generated.FunctionalChunk0298.valid
  · exact leaf866 hRep
  · exact leaf867 hRep
  · exact leaf868 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0298

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0299
def descriptor869 : OrbitDescriptor := ⟨65, 13, false⟩

theorem checked869 : orbitPatternTransform descriptor869 (Generated.Chunk0299.pattern869) =
    orbitRepresentativePattern descriptor869.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf869 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0299.pattern869 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0299.pattern869) descriptor869 checked869 (hRep descriptor869.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0299.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0299.regionContext := by
  apply Generated.FunctionalChunk0299.valid
  · exact leaf869 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0299

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0300
def descriptor870 : OrbitDescriptor := ⟨32, 10, true⟩

theorem checked870 : orbitPatternTransform descriptor870 (Generated.Chunk0300.pattern870) =
    orbitRepresentativePattern descriptor870.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf870 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0300.pattern870 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0300.pattern870) descriptor870 checked870 (hRep descriptor870.representative)

def descriptor871 : OrbitDescriptor := ⟨31, 10, true⟩

theorem checked871 : orbitPatternTransform descriptor871 (Generated.Chunk0300.pattern871) =
    orbitRepresentativePattern descriptor871.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf871 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0300.pattern871 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0300.pattern871) descriptor871 checked871 (hRep descriptor871.representative)

def descriptor872 : OrbitDescriptor := ⟨29, 20, true⟩

theorem checked872 : orbitPatternTransform descriptor872 (Generated.Chunk0300.pattern872) =
    orbitRepresentativePattern descriptor872.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf872 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0300.pattern872 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0300.pattern872) descriptor872 checked872 (hRep descriptor872.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0300.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0300.regionContext := by
  apply Generated.FunctionalChunk0300.valid
  · exact leaf870 hRep
  · exact leaf871 hRep
  · exact leaf872 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0300

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0301
def descriptor873 : OrbitDescriptor := ⟨30, 22, false⟩

theorem checked873 : orbitPatternTransform descriptor873 (Generated.Chunk0301.pattern873) =
    orbitRepresentativePattern descriptor873.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf873 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0301.pattern873 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0301.pattern873) descriptor873 checked873 (hRep descriptor873.representative)

def descriptor874 : OrbitDescriptor := ⟨32, 22, false⟩

theorem checked874 : orbitPatternTransform descriptor874 (Generated.Chunk0301.pattern874) =
    orbitRepresentativePattern descriptor874.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf874 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0301.pattern874 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0301.pattern874) descriptor874 checked874 (hRep descriptor874.representative)

def descriptor875 : OrbitDescriptor := ⟨33, 16, false⟩

theorem checked875 : orbitPatternTransform descriptor875 (Generated.Chunk0301.pattern875) =
    orbitRepresentativePattern descriptor875.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf875 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0301.pattern875 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0301.pattern875) descriptor875 checked875 (hRep descriptor875.representative)

def descriptor876 : OrbitDescriptor := ⟨34, 16, false⟩

theorem checked876 : orbitPatternTransform descriptor876 (Generated.Chunk0301.pattern876) =
    orbitRepresentativePattern descriptor876.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf876 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0301.pattern876 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0301.pattern876) descriptor876 checked876 (hRep descriptor876.representative)

def descriptor877 : OrbitDescriptor := ⟨35, 16, false⟩

theorem checked877 : orbitPatternTransform descriptor877 (Generated.Chunk0301.pattern877) =
    orbitRepresentativePattern descriptor877.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf877 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0301.pattern877 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0301.pattern877) descriptor877 checked877 (hRep descriptor877.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0301.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0301.regionContext := by
  apply Generated.FunctionalChunk0301.valid
  · exact leaf873 hRep
  · exact leaf874 hRep
  · exact leaf875 hRep
  · exact leaf876 hRep
  · exact leaf877 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0301

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0302
def descriptor878 : OrbitDescriptor := ⟨64, 7, true⟩

theorem checked878 : orbitPatternTransform descriptor878 (Generated.Chunk0302.pattern878) =
    orbitRepresentativePattern descriptor878.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf878 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0302.pattern878 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0302.pattern878) descriptor878 checked878 (hRep descriptor878.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0302.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0302.regionContext := by
  apply Generated.FunctionalChunk0302.valid
  · exact leaf878 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0302

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0303
def descriptor879 : OrbitDescriptor := ⟨30, 10, true⟩

theorem checked879 : orbitPatternTransform descriptor879 (Generated.Chunk0303.pattern879) =
    orbitRepresentativePattern descriptor879.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf879 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0303.pattern879 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0303.pattern879) descriptor879 checked879 (hRep descriptor879.representative)

def descriptor880 : OrbitDescriptor := ⟨29, 10, true⟩

theorem checked880 : orbitPatternTransform descriptor880 (Generated.Chunk0303.pattern880) =
    orbitRepresentativePattern descriptor880.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf880 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0303.pattern880 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0303.pattern880) descriptor880 checked880 (hRep descriptor880.representative)

def descriptor881 : OrbitDescriptor := ⟨28, 10, true⟩

theorem checked881 : orbitPatternTransform descriptor881 (Generated.Chunk0303.pattern881) =
    orbitRepresentativePattern descriptor881.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf881 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0303.pattern881 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0303.pattern881) descriptor881 checked881 (hRep descriptor881.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0303.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0303.regionContext := by
  apply Generated.FunctionalChunk0303.valid
  · exact leaf879 hRep
  · exact leaf880 hRep
  · exact leaf881 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0303
