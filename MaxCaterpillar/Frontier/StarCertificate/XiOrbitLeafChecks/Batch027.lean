import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0216
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0217
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0218
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0219
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0220
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0221
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0222
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0223
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0216
def descriptor626 : OrbitDescriptor := ⟨54, 10, true⟩

theorem checked626 : orbitPatternTransform descriptor626 (Generated.Chunk0216.pattern626) =
    orbitRepresentativePattern descriptor626.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf626 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0216.pattern626 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0216.pattern626) descriptor626 checked626 (hRep descriptor626.representative)

def descriptor627 : OrbitDescriptor := ⟨53, 10, true⟩

theorem checked627 : orbitPatternTransform descriptor627 (Generated.Chunk0216.pattern627) =
    orbitRepresentativePattern descriptor627.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf627 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0216.pattern627 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0216.pattern627) descriptor627 checked627 (hRep descriptor627.representative)

def descriptor628 : OrbitDescriptor := ⟨52, 10, true⟩

theorem checked628 : orbitPatternTransform descriptor628 (Generated.Chunk0216.pattern628) =
    orbitRepresentativePattern descriptor628.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf628 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0216.pattern628 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0216.pattern628) descriptor628 checked628 (hRep descriptor628.representative)

def descriptor629 : OrbitDescriptor := ⟨51, 10, true⟩

theorem checked629 : orbitPatternTransform descriptor629 (Generated.Chunk0216.pattern629) =
    orbitRepresentativePattern descriptor629.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf629 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0216.pattern629 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0216.pattern629) descriptor629 checked629 (hRep descriptor629.representative)

def descriptor630 : OrbitDescriptor := ⟨50, 10, true⟩

theorem checked630 : orbitPatternTransform descriptor630 (Generated.Chunk0216.pattern630) =
    orbitRepresentativePattern descriptor630.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf630 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0216.pattern630 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0216.pattern630) descriptor630 checked630 (hRep descriptor630.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0216.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0216.regionContext := by
  apply Generated.FunctionalChunk0216.valid
  · exact leaf626 hRep
  · exact leaf627 hRep
  · exact leaf628 hRep
  · exact leaf629 hRep
  · exact leaf630 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0216

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0217
def descriptor631 : OrbitDescriptor := ⟨49, 20, true⟩

theorem checked631 : orbitPatternTransform descriptor631 (Generated.Chunk0217.pattern631) =
    orbitRepresentativePattern descriptor631.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf631 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0217.pattern631 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0217.pattern631) descriptor631 checked631 (hRep descriptor631.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0217.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0217.regionContext := by
  apply Generated.FunctionalChunk0217.valid
  · exact leaf631 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0217

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0218
def descriptor632 : OrbitDescriptor := ⟨47, 20, true⟩

theorem checked632 : orbitPatternTransform descriptor632 (Generated.Chunk0218.pattern632) =
    orbitRepresentativePattern descriptor632.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf632 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0218.pattern632 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0218.pattern632) descriptor632 checked632 (hRep descriptor632.representative)

def descriptor633 : OrbitDescriptor := ⟨46, 20, true⟩

theorem checked633 : orbitPatternTransform descriptor633 (Generated.Chunk0218.pattern633) =
    orbitRepresentativePattern descriptor633.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf633 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0218.pattern633 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0218.pattern633) descriptor633 checked633 (hRep descriptor633.representative)

def descriptor634 : OrbitDescriptor := ⟨45, 20, true⟩

theorem checked634 : orbitPatternTransform descriptor634 (Generated.Chunk0218.pattern634) =
    orbitRepresentativePattern descriptor634.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf634 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0218.pattern634 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0218.pattern634) descriptor634 checked634 (hRep descriptor634.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0218.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0218.regionContext := by
  apply Generated.FunctionalChunk0218.valid
  · exact leaf632 hRep
  · exact leaf633 hRep
  · exact leaf634 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0218

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0219
def descriptor635 : OrbitDescriptor := ⟨6, 22, false⟩

theorem checked635 : orbitPatternTransform descriptor635 (Generated.Chunk0219.pattern635) =
    orbitRepresentativePattern descriptor635.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf635 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0219.pattern635 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0219.pattern635) descriptor635 checked635 (hRep descriptor635.representative)

def descriptor636 : OrbitDescriptor := ⟨11, 16, false⟩

theorem checked636 : orbitPatternTransform descriptor636 (Generated.Chunk0219.pattern636) =
    orbitRepresentativePattern descriptor636.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf636 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0219.pattern636 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0219.pattern636) descriptor636 checked636 (hRep descriptor636.representative)

def descriptor637 : OrbitDescriptor := ⟨12, 13, false⟩

theorem checked637 : orbitPatternTransform descriptor637 (Generated.Chunk0219.pattern637) =
    orbitRepresentativePattern descriptor637.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf637 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0219.pattern637 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0219.pattern637) descriptor637 checked637 (hRep descriptor637.representative)

def descriptor638 : OrbitDescriptor := ⟨13, 13, false⟩

theorem checked638 : orbitPatternTransform descriptor638 (Generated.Chunk0219.pattern638) =
    orbitRepresentativePattern descriptor638.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf638 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0219.pattern638 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0219.pattern638) descriptor638 checked638 (hRep descriptor638.representative)

def descriptor639 : OrbitDescriptor := ⟨14, 13, false⟩

theorem checked639 : orbitPatternTransform descriptor639 (Generated.Chunk0219.pattern639) =
    orbitRepresentativePattern descriptor639.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf639 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0219.pattern639 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0219.pattern639) descriptor639 checked639 (hRep descriptor639.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0219.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0219.regionContext := by
  apply Generated.FunctionalChunk0219.valid
  · exact leaf635 hRep
  · exact leaf636 hRep
  · exact leaf637 hRep
  · exact leaf638 hRep
  · exact leaf639 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0219

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0220
def descriptor640 : OrbitDescriptor := ⟨32, 13, false⟩

theorem checked640 : orbitPatternTransform descriptor640 (Generated.Chunk0220.pattern640) =
    orbitRepresentativePattern descriptor640.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf640 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0220.pattern640 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0220.pattern640) descriptor640 checked640 (hRep descriptor640.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0220.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0220.regionContext := by
  apply Generated.FunctionalChunk0220.valid
  · exact leaf640 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0220

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0221
def descriptor641 : OrbitDescriptor := ⟨49, 13, false⟩

theorem checked641 : orbitPatternTransform descriptor641 (Generated.Chunk0221.pattern641) =
    orbitRepresentativePattern descriptor641.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf641 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0221.pattern641 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0221.pattern641) descriptor641 checked641 (hRep descriptor641.representative)

def descriptor642 : OrbitDescriptor := ⟨61, 13, false⟩

theorem checked642 : orbitPatternTransform descriptor642 (Generated.Chunk0221.pattern642) =
    orbitRepresentativePattern descriptor642.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf642 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0221.pattern642 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0221.pattern642) descriptor642 checked642 (hRep descriptor642.representative)

def descriptor643 : OrbitDescriptor := ⟨49, 10, true⟩

theorem checked643 : orbitPatternTransform descriptor643 (Generated.Chunk0221.pattern643) =
    orbitRepresentativePattern descriptor643.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf643 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0221.pattern643 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0221.pattern643) descriptor643 checked643 (hRep descriptor643.representative)

def descriptor644 : OrbitDescriptor := ⟨48, 10, true⟩

theorem checked644 : orbitPatternTransform descriptor644 (Generated.Chunk0221.pattern644) =
    orbitRepresentativePattern descriptor644.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf644 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0221.pattern644 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0221.pattern644) descriptor644 checked644 (hRep descriptor644.representative)

def descriptor645 : OrbitDescriptor := ⟨44, 20, true⟩

theorem checked645 : orbitPatternTransform descriptor645 (Generated.Chunk0221.pattern645) =
    orbitRepresentativePattern descriptor645.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf645 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0221.pattern645 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0221.pattern645) descriptor645 checked645 (hRep descriptor645.representative)

def descriptor646 : OrbitDescriptor := ⟨43, 20, true⟩

theorem checked646 : orbitPatternTransform descriptor646 (Generated.Chunk0221.pattern646) =
    orbitRepresentativePattern descriptor646.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf646 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0221.pattern646 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0221.pattern646) descriptor646 checked646 (hRep descriptor646.representative)

def descriptor647 : OrbitDescriptor := ⟨42, 20, true⟩

theorem checked647 : orbitPatternTransform descriptor647 (Generated.Chunk0221.pattern647) =
    orbitRepresentativePattern descriptor647.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf647 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0221.pattern647 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0221.pattern647) descriptor647 checked647 (hRep descriptor647.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0221.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0221.regionContext := by
  apply Generated.FunctionalChunk0221.valid
  · exact leaf641 hRep
  · exact leaf642 hRep
  · exact leaf643 hRep
  · exact leaf644 hRep
  · exact leaf645 hRep
  · exact leaf646 hRep
  · exact leaf647 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0221

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0222
def descriptor648 : OrbitDescriptor := ⟨7, 19, false⟩

theorem checked648 : orbitPatternTransform descriptor648 (Generated.Chunk0222.pattern648) =
    orbitRepresentativePattern descriptor648.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf648 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0222.pattern648 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0222.pattern648) descriptor648 checked648 (hRep descriptor648.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0222.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0222.regionContext := by
  apply Generated.FunctionalChunk0222.valid
  · exact leaf648 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0222

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0223
def descriptor649 : OrbitDescriptor := ⟨12, 19, false⟩

theorem checked649 : orbitPatternTransform descriptor649 (Generated.Chunk0223.pattern649) =
    orbitRepresentativePattern descriptor649.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf649 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0223.pattern649 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0223.pattern649) descriptor649 checked649 (hRep descriptor649.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0223.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0223.regionContext := by
  apply Generated.FunctionalChunk0223.valid
  · exact leaf649 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0223
