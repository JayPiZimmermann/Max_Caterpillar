import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0232
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0233
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0234
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0235
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0236
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0237
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0238
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0239
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0232
def descriptor674 : OrbitDescriptor := ⟨13, 19, false⟩

theorem checked674 : orbitPatternTransform descriptor674 (Generated.Chunk0232.pattern674) =
    orbitRepresentativePattern descriptor674.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf674 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0232.pattern674 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0232.pattern674) descriptor674 checked674 (hRep descriptor674.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0232.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0232.regionContext := by
  apply Generated.FunctionalChunk0232.valid
  · exact leaf674 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0232

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0233
def descriptor675 : OrbitDescriptor := ⟨16, 19, false⟩

theorem checked675 : orbitPatternTransform descriptor675 (Generated.Chunk0233.pattern675) =
    orbitRepresentativePattern descriptor675.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf675 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0233.pattern675 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0233.pattern675) descriptor675 checked675 (hRep descriptor675.representative)

def descriptor676 : OrbitDescriptor := ⟨18, 5, false⟩

theorem checked676 : orbitPatternTransform descriptor676 (Generated.Chunk0233.pattern676) =
    orbitRepresentativePattern descriptor676.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf676 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0233.pattern676 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0233.pattern676) descriptor676 checked676 (hRep descriptor676.representative)

def descriptor677 : OrbitDescriptor := ⟨19, 5, false⟩

theorem checked677 : orbitPatternTransform descriptor677 (Generated.Chunk0233.pattern677) =
    orbitRepresentativePattern descriptor677.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf677 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0233.pattern677 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0233.pattern677) descriptor677 checked677 (hRep descriptor677.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0233.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0233.regionContext := by
  apply Generated.FunctionalChunk0233.valid
  · exact leaf675 hRep
  · exact leaf676 hRep
  · exact leaf677 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0233

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0234
def descriptor678 : OrbitDescriptor := ⟨18, 16, false⟩

theorem checked678 : orbitPatternTransform descriptor678 (Generated.Chunk0234.pattern678) =
    orbitRepresentativePattern descriptor678.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf678 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0234.pattern678 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0234.pattern678) descriptor678 checked678 (hRep descriptor678.representative)

def descriptor679 : OrbitDescriptor := ⟨21, 3, false⟩

theorem checked679 : orbitPatternTransform descriptor679 (Generated.Chunk0234.pattern679) =
    orbitRepresentativePattern descriptor679.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf679 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0234.pattern679 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0234.pattern679) descriptor679 checked679 (hRep descriptor679.representative)

def descriptor680 : OrbitDescriptor := ⟨22, 3, false⟩

theorem checked680 : orbitPatternTransform descriptor680 (Generated.Chunk0234.pattern680) =
    orbitRepresentativePattern descriptor680.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf680 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0234.pattern680 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0234.pattern680) descriptor680 checked680 (hRep descriptor680.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0234.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0234.regionContext := by
  apply Generated.FunctionalChunk0234.valid
  · exact leaf678 hRep
  · exact leaf679 hRep
  · exact leaf680 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0234

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0235
def descriptor681 : OrbitDescriptor := ⟨19, 16, false⟩

theorem checked681 : orbitPatternTransform descriptor681 (Generated.Chunk0235.pattern681) =
    orbitRepresentativePattern descriptor681.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf681 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0235.pattern681 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0235.pattern681) descriptor681 checked681 (hRep descriptor681.representative)

def descriptor682 : OrbitDescriptor := ⟨22, 13, false⟩

theorem checked682 : orbitPatternTransform descriptor682 (Generated.Chunk0235.pattern682) =
    orbitRepresentativePattern descriptor682.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf682 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0235.pattern682 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0235.pattern682) descriptor682 checked682 (hRep descriptor682.representative)

def descriptor683 : OrbitDescriptor := ⟨23, 3, false⟩

theorem checked683 : orbitPatternTransform descriptor683 (Generated.Chunk0235.pattern683) =
    orbitRepresentativePattern descriptor683.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf683 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0235.pattern683 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0235.pattern683) descriptor683 checked683 (hRep descriptor683.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0235.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0235.regionContext := by
  apply Generated.FunctionalChunk0235.valid
  · exact leaf681 hRep
  · exact leaf682 hRep
  · exact leaf683 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0235

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0236
def descriptor684 : OrbitDescriptor := ⟨34, 3, false⟩

theorem checked684 : orbitPatternTransform descriptor684 (Generated.Chunk0236.pattern684) =
    orbitRepresentativePattern descriptor684.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf684 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0236.pattern684 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0236.pattern684) descriptor684 checked684 (hRep descriptor684.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0236.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0236.regionContext := by
  apply Generated.FunctionalChunk0236.valid
  · exact leaf684 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0236

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0237
def descriptor685 : OrbitDescriptor := ⟨53, 3, false⟩

theorem checked685 : orbitPatternTransform descriptor685 (Generated.Chunk0237.pattern685) =
    orbitRepresentativePattern descriptor685.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf685 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0237.pattern685 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0237.pattern685) descriptor685 checked685 (hRep descriptor685.representative)

def descriptor686 : OrbitDescriptor := ⟨59, 11, true⟩

theorem checked686 : orbitPatternTransform descriptor686 (Generated.Chunk0237.pattern686) =
    orbitRepresentativePattern descriptor686.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf686 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0237.pattern686 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0237.pattern686) descriptor686 checked686 (hRep descriptor686.representative)

def descriptor687 : OrbitDescriptor := ⟨46, 11, true⟩

theorem checked687 : orbitPatternTransform descriptor687 (Generated.Chunk0237.pattern687) =
    orbitRepresentativePattern descriptor687.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf687 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0237.pattern687 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0237.pattern687) descriptor687 checked687 (hRep descriptor687.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0237.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0237.regionContext := by
  apply Generated.FunctionalChunk0237.valid
  · exact leaf685 hRep
  · exact leaf686 hRep
  · exact leaf687 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0237

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0238
def descriptor688 : OrbitDescriptor := ⟨59, 10, true⟩

theorem checked688 : orbitPatternTransform descriptor688 (Generated.Chunk0238.pattern688) =
    orbitRepresentativePattern descriptor688.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf688 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0238.pattern688 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0238.pattern688) descriptor688 checked688 (hRep descriptor688.representative)

def descriptor689 : OrbitDescriptor := ⟨56, 10, true⟩

theorem checked689 : orbitPatternTransform descriptor689 (Generated.Chunk0238.pattern689) =
    orbitRepresentativePattern descriptor689.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf689 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0238.pattern689 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0238.pattern689) descriptor689 checked689 (hRep descriptor689.representative)

def descriptor690 : OrbitDescriptor := ⟨43, 11, true⟩

theorem checked690 : orbitPatternTransform descriptor690 (Generated.Chunk0238.pattern690) =
    orbitRepresentativePattern descriptor690.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf690 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0238.pattern690 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0238.pattern690) descriptor690 checked690 (hRep descriptor690.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0238.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0238.regionContext := by
  apply Generated.FunctionalChunk0238.valid
  · exact leaf688 hRep
  · exact leaf689 hRep
  · exact leaf690 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0238

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0239
def descriptor691 : OrbitDescriptor := ⟨46, 10, true⟩

theorem checked691 : orbitPatternTransform descriptor691 (Generated.Chunk0239.pattern691) =
    orbitRepresentativePattern descriptor691.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf691 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0239.pattern691 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0239.pattern691) descriptor691 checked691 (hRep descriptor691.representative)

def descriptor692 : OrbitDescriptor := ⟨43, 10, true⟩

theorem checked692 : orbitPatternTransform descriptor692 (Generated.Chunk0239.pattern692) =
    orbitRepresentativePattern descriptor692.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf692 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0239.pattern692 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0239.pattern692) descriptor692 checked692 (hRep descriptor692.representative)

def descriptor693 : OrbitDescriptor := ⟨40, 10, true⟩

theorem checked693 : orbitPatternTransform descriptor693 (Generated.Chunk0239.pattern693) =
    orbitRepresentativePattern descriptor693.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf693 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0239.pattern693 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0239.pattern693) descriptor693 checked693 (hRep descriptor693.representative)

def descriptor694 : OrbitDescriptor := ⟨39, 10, true⟩

theorem checked694 : orbitPatternTransform descriptor694 (Generated.Chunk0239.pattern694) =
    orbitRepresentativePattern descriptor694.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf694 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0239.pattern694 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0239.pattern694) descriptor694 checked694 (hRep descriptor694.representative)

def descriptor695 : OrbitDescriptor := ⟨37, 20, true⟩

theorem checked695 : orbitPatternTransform descriptor695 (Generated.Chunk0239.pattern695) =
    orbitRepresentativePattern descriptor695.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf695 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0239.pattern695 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0239.pattern695) descriptor695 checked695 (hRep descriptor695.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0239.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0239.regionContext := by
  apply Generated.FunctionalChunk0239.valid
  · exact leaf691 hRep
  · exact leaf692 hRep
  · exact leaf693 hRep
  · exact leaf694 hRep
  · exact leaf695 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0239
