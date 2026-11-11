import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0248
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0249
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0250
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0251
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0252
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0253
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0254
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0255
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0248
def descriptor716 : OrbitDescriptor := ⟨45, 10, true⟩

theorem checked716 : orbitPatternTransform descriptor716 (Generated.Chunk0248.pattern716) =
    orbitRepresentativePattern descriptor716.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf716 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0248.pattern716 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0248.pattern716) descriptor716 checked716 (hRep descriptor716.representative)

def descriptor717 : OrbitDescriptor := ⟨42, 10, true⟩

theorem checked717 : orbitPatternTransform descriptor717 (Generated.Chunk0248.pattern717) =
    orbitRepresentativePattern descriptor717.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf717 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0248.pattern717 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0248.pattern717) descriptor717 checked717 (hRep descriptor717.representative)

def descriptor718 : OrbitDescriptor := ⟨38, 10, true⟩

theorem checked718 : orbitPatternTransform descriptor718 (Generated.Chunk0248.pattern718) =
    orbitRepresentativePattern descriptor718.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf718 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0248.pattern718 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0248.pattern718) descriptor718 checked718 (hRep descriptor718.representative)

def descriptor719 : OrbitDescriptor := ⟨37, 10, true⟩

theorem checked719 : orbitPatternTransform descriptor719 (Generated.Chunk0248.pattern719) =
    orbitRepresentativePattern descriptor719.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf719 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0248.pattern719 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0248.pattern719) descriptor719 checked719 (hRep descriptor719.representative)

def descriptor720 : OrbitDescriptor := ⟨36, 10, true⟩

theorem checked720 : orbitPatternTransform descriptor720 (Generated.Chunk0248.pattern720) =
    orbitRepresentativePattern descriptor720.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf720 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0248.pattern720 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0248.pattern720) descriptor720 checked720 (hRep descriptor720.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0248.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0248.regionContext := by
  apply Generated.FunctionalChunk0248.valid
  · exact leaf716 hRep
  · exact leaf717 hRep
  · exact leaf718 hRep
  · exact leaf719 hRep
  · exact leaf720 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0248

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0249
def descriptor721 : OrbitDescriptor := ⟨30, 19, false⟩

theorem checked721 : orbitPatternTransform descriptor721 (Generated.Chunk0249.pattern721) =
    orbitRepresentativePattern descriptor721.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf721 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0249.pattern721 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0249.pattern721) descriptor721 checked721 (hRep descriptor721.representative)

def descriptor722 : OrbitDescriptor := ⟨32, 19, false⟩

theorem checked722 : orbitPatternTransform descriptor722 (Generated.Chunk0249.pattern722) =
    orbitRepresentativePattern descriptor722.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf722 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0249.pattern722 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0249.pattern722) descriptor722 checked722 (hRep descriptor722.representative)

def descriptor723 : OrbitDescriptor := ⟨33, 5, false⟩

theorem checked723 : orbitPatternTransform descriptor723 (Generated.Chunk0249.pattern723) =
    orbitRepresentativePattern descriptor723.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf723 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0249.pattern723 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0249.pattern723) descriptor723 checked723 (hRep descriptor723.representative)

def descriptor724 : OrbitDescriptor := ⟨34, 5, false⟩

theorem checked724 : orbitPatternTransform descriptor724 (Generated.Chunk0249.pattern724) =
    orbitRepresentativePattern descriptor724.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf724 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0249.pattern724 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0249.pattern724) descriptor724 checked724 (hRep descriptor724.representative)

def descriptor725 : OrbitDescriptor := ⟨35, 5, false⟩

theorem checked725 : orbitPatternTransform descriptor725 (Generated.Chunk0249.pattern725) =
    orbitRepresentativePattern descriptor725.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf725 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0249.pattern725 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0249.pattern725) descriptor725 checked725 (hRep descriptor725.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0249.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0249.regionContext := by
  apply Generated.FunctionalChunk0249.valid
  · exact leaf721 hRep
  · exact leaf722 hRep
  · exact leaf723 hRep
  · exact leaf724 hRep
  · exact leaf725 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0249

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0250
def descriptor726 : OrbitDescriptor := ⟨64, 9, true⟩

theorem checked726 : orbitPatternTransform descriptor726 (Generated.Chunk0250.pattern726) =
    orbitRepresentativePattern descriptor726.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf726 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0250.pattern726 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0250.pattern726) descriptor726 checked726 (hRep descriptor726.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0250.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0250.regionContext := by
  apply Generated.FunctionalChunk0250.valid
  · exact leaf726 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0250

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0251
def descriptor727 : OrbitDescriptor := ⟨30, 11, true⟩

theorem checked727 : orbitPatternTransform descriptor727 (Generated.Chunk0251.pattern727) =
    orbitRepresentativePattern descriptor727.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf727 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0251.pattern727 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0251.pattern727) descriptor727 checked727 (hRep descriptor727.representative)

def descriptor728 : OrbitDescriptor := ⟨29, 11, true⟩

theorem checked728 : orbitPatternTransform descriptor728 (Generated.Chunk0251.pattern728) =
    orbitRepresentativePattern descriptor728.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf728 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0251.pattern728 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0251.pattern728) descriptor728 checked728 (hRep descriptor728.representative)

def descriptor729 : OrbitDescriptor := ⟨28, 11, true⟩

theorem checked729 : orbitPatternTransform descriptor729 (Generated.Chunk0251.pattern729) =
    orbitRepresentativePattern descriptor729.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf729 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0251.pattern729 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0251.pattern729) descriptor729 checked729 (hRep descriptor729.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0251.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0251.regionContext := by
  apply Generated.FunctionalChunk0251.valid
  · exact leaf727 hRep
  · exact leaf728 hRep
  · exact leaf729 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0251

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0252
def descriptor730 : OrbitDescriptor := ⟨45, 19, false⟩

theorem checked730 : orbitPatternTransform descriptor730 (Generated.Chunk0252.pattern730) =
    orbitRepresentativePattern descriptor730.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf730 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0252.pattern730 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0252.pattern730) descriptor730 checked730 (hRep descriptor730.representative)

def descriptor731 : OrbitDescriptor := ⟨46, 19, false⟩

theorem checked731 : orbitPatternTransform descriptor731 (Generated.Chunk0252.pattern731) =
    orbitRepresentativePattern descriptor731.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf731 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0252.pattern731 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0252.pattern731) descriptor731 checked731 (hRep descriptor731.representative)

def descriptor732 : OrbitDescriptor := ⟨47, 19, false⟩

theorem checked732 : orbitPatternTransform descriptor732 (Generated.Chunk0252.pattern732) =
    orbitRepresentativePattern descriptor732.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf732 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0252.pattern732 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0252.pattern732) descriptor732 checked732 (hRep descriptor732.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0252.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0252.regionContext := by
  apply Generated.FunctionalChunk0252.valid
  · exact leaf730 hRep
  · exact leaf731 hRep
  · exact leaf732 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0252

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0253
def descriptor733 : OrbitDescriptor := ⟨49, 19, false⟩

theorem checked733 : orbitPatternTransform descriptor733 (Generated.Chunk0253.pattern733) =
    orbitRepresentativePattern descriptor733.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf733 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0253.pattern733 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0253.pattern733) descriptor733 checked733 (hRep descriptor733.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0253.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0253.regionContext := by
  apply Generated.FunctionalChunk0253.valid
  · exact leaf733 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0253

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0254
def descriptor734 : OrbitDescriptor := ⟨50, 5, false⟩

theorem checked734 : orbitPatternTransform descriptor734 (Generated.Chunk0254.pattern734) =
    orbitRepresentativePattern descriptor734.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf734 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0254.pattern734 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0254.pattern734) descriptor734 checked734 (hRep descriptor734.representative)

def descriptor735 : OrbitDescriptor := ⟨51, 5, false⟩

theorem checked735 : orbitPatternTransform descriptor735 (Generated.Chunk0254.pattern735) =
    orbitRepresentativePattern descriptor735.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf735 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0254.pattern735 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0254.pattern735) descriptor735 checked735 (hRep descriptor735.representative)

def descriptor736 : OrbitDescriptor := ⟨52, 5, false⟩

theorem checked736 : orbitPatternTransform descriptor736 (Generated.Chunk0254.pattern736) =
    orbitRepresentativePattern descriptor736.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf736 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0254.pattern736 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0254.pattern736) descriptor736 checked736 (hRep descriptor736.representative)

def descriptor737 : OrbitDescriptor := ⟨60, 9, true⟩

theorem checked737 : orbitPatternTransform descriptor737 (Generated.Chunk0254.pattern737) =
    orbitRepresentativePattern descriptor737.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf737 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0254.pattern737 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0254.pattern737) descriptor737 checked737 (hRep descriptor737.representative)

def descriptor738 : OrbitDescriptor := ⟨47, 9, true⟩

theorem checked738 : orbitPatternTransform descriptor738 (Generated.Chunk0254.pattern738) =
    orbitRepresentativePattern descriptor738.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf738 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0254.pattern738 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0254.pattern738) descriptor738 checked738 (hRep descriptor738.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0254.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0254.regionContext := by
  apply Generated.FunctionalChunk0254.valid
  · exact leaf734 hRep
  · exact leaf735 hRep
  · exact leaf736 hRep
  · exact leaf737 hRep
  · exact leaf738 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0254

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0255
def descriptor739 : OrbitDescriptor := ⟨53, 5, false⟩

theorem checked739 : orbitPatternTransform descriptor739 (Generated.Chunk0255.pattern739) =
    orbitRepresentativePattern descriptor739.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf739 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0255.pattern739 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0255.pattern739) descriptor739 checked739 (hRep descriptor739.representative)

def descriptor740 : OrbitDescriptor := ⟨59, 9, true⟩

theorem checked740 : orbitPatternTransform descriptor740 (Generated.Chunk0255.pattern740) =
    orbitRepresentativePattern descriptor740.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf740 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0255.pattern740 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0255.pattern740) descriptor740 checked740 (hRep descriptor740.representative)

def descriptor741 : OrbitDescriptor := ⟨46, 9, true⟩

theorem checked741 : orbitPatternTransform descriptor741 (Generated.Chunk0255.pattern741) =
    orbitRepresentativePattern descriptor741.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf741 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0255.pattern741 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0255.pattern741) descriptor741 checked741 (hRep descriptor741.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0255.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0255.regionContext := by
  apply Generated.FunctionalChunk0255.valid
  · exact leaf739 hRep
  · exact leaf740 hRep
  · exact leaf741 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0255
