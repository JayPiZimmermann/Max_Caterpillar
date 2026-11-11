import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0224
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0225
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0226
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0227
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0228
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0229
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0230
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0231
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0224
def descriptor650 : OrbitDescriptor := ⟨15, 3, false⟩

theorem checked650 : orbitPatternTransform descriptor650 (Generated.Chunk0224.pattern650) =
    orbitRepresentativePattern descriptor650.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf650 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0224.pattern650 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0224.pattern650) descriptor650 checked650 (hRep descriptor650.representative)

def descriptor651 : OrbitDescriptor := ⟨16, 3, false⟩

theorem checked651 : orbitPatternTransform descriptor651 (Generated.Chunk0224.pattern651) =
    orbitRepresentativePattern descriptor651.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf651 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0224.pattern651 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0224.pattern651) descriptor651 checked651 (hRep descriptor651.representative)

def descriptor652 : OrbitDescriptor := ⟨17, 3, false⟩

theorem checked652 : orbitPatternTransform descriptor652 (Generated.Chunk0224.pattern652) =
    orbitRepresentativePattern descriptor652.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf652 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0224.pattern652 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0224.pattern652) descriptor652 checked652 (hRep descriptor652.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0224.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0224.regionContext := by
  apply Generated.FunctionalChunk0224.valid
  · exact leaf650 hRep
  · exact leaf651 hRep
  · exact leaf652 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0224

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0225
def descriptor653 : OrbitDescriptor := ⟨16, 13, false⟩

theorem checked653 : orbitPatternTransform descriptor653 (Generated.Chunk0225.pattern653) =
    orbitRepresentativePattern descriptor653.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf653 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0225.pattern653 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0225.pattern653) descriptor653 checked653 (hRep descriptor653.representative)

def descriptor654 : OrbitDescriptor := ⟨18, 3, false⟩

theorem checked654 : orbitPatternTransform descriptor654 (Generated.Chunk0225.pattern654) =
    orbitRepresentativePattern descriptor654.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf654 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0225.pattern654 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0225.pattern654) descriptor654 checked654 (hRep descriptor654.representative)

def descriptor655 : OrbitDescriptor := ⟨19, 3, false⟩

theorem checked655 : orbitPatternTransform descriptor655 (Generated.Chunk0225.pattern655) =
    orbitRepresentativePattern descriptor655.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf655 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0225.pattern655 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0225.pattern655) descriptor655 checked655 (hRep descriptor655.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0225.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0225.regionContext := by
  apply Generated.FunctionalChunk0225.valid
  · exact leaf653 hRep
  · exact leaf654 hRep
  · exact leaf655 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0225

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0226
def descriptor656 : OrbitDescriptor := ⟨17, 13, false⟩

theorem checked656 : orbitPatternTransform descriptor656 (Generated.Chunk0226.pattern656) =
    orbitRepresentativePattern descriptor656.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf656 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0226.pattern656 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0226.pattern656) descriptor656 checked656 (hRep descriptor656.representative)

def descriptor657 : OrbitDescriptor := ⟨19, 13, false⟩

theorem checked657 : orbitPatternTransform descriptor657 (Generated.Chunk0226.pattern657) =
    orbitRepresentativePattern descriptor657.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf657 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0226.pattern657 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0226.pattern657) descriptor657 checked657 (hRep descriptor657.representative)

def descriptor658 : OrbitDescriptor := ⟨20, 3, false⟩

theorem checked658 : orbitPatternTransform descriptor658 (Generated.Chunk0226.pattern658) =
    orbitRepresentativePattern descriptor658.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf658 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0226.pattern658 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0226.pattern658) descriptor658 checked658 (hRep descriptor658.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0226.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0226.regionContext := by
  apply Generated.FunctionalChunk0226.valid
  · exact leaf656 hRep
  · exact leaf657 hRep
  · exact leaf658 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0226

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0227
def descriptor659 : OrbitDescriptor := ⟨33, 3, false⟩

theorem checked659 : orbitPatternTransform descriptor659 (Generated.Chunk0227.pattern659) =
    orbitRepresentativePattern descriptor659.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf659 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0227.pattern659 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0227.pattern659) descriptor659 checked659 (hRep descriptor659.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0227.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0227.regionContext := by
  apply Generated.FunctionalChunk0227.valid
  · exact leaf659 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0227

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0228
def descriptor660 : OrbitDescriptor := ⟨50, 3, false⟩

theorem checked660 : orbitPatternTransform descriptor660 (Generated.Chunk0228.pattern660) =
    orbitRepresentativePattern descriptor660.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf660 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0228.pattern660 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0228.pattern660) descriptor660 checked660 (hRep descriptor660.representative)

def descriptor661 : OrbitDescriptor := ⟨51, 3, false⟩

theorem checked661 : orbitPatternTransform descriptor661 (Generated.Chunk0228.pattern661) =
    orbitRepresentativePattern descriptor661.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf661 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0228.pattern661 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0228.pattern661) descriptor661 checked661 (hRep descriptor661.representative)

def descriptor662 : OrbitDescriptor := ⟨52, 3, false⟩

theorem checked662 : orbitPatternTransform descriptor662 (Generated.Chunk0228.pattern662) =
    orbitRepresentativePattern descriptor662.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf662 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0228.pattern662 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0228.pattern662) descriptor662 checked662 (hRep descriptor662.representative)

def descriptor663 : OrbitDescriptor := ⟨60, 11, true⟩

theorem checked663 : orbitPatternTransform descriptor663 (Generated.Chunk0228.pattern663) =
    orbitRepresentativePattern descriptor663.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf663 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0228.pattern663 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0228.pattern663) descriptor663 checked663 (hRep descriptor663.representative)

def descriptor664 : OrbitDescriptor := ⟨47, 11, true⟩

theorem checked664 : orbitPatternTransform descriptor664 (Generated.Chunk0228.pattern664) =
    orbitRepresentativePattern descriptor664.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf664 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0228.pattern664 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0228.pattern664) descriptor664 checked664 (hRep descriptor664.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0228.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0228.regionContext := by
  apply Generated.FunctionalChunk0228.valid
  · exact leaf660 hRep
  · exact leaf661 hRep
  · exact leaf662 hRep
  · exact leaf663 hRep
  · exact leaf664 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0228

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0229
def descriptor665 : OrbitDescriptor := ⟨60, 10, true⟩

theorem checked665 : orbitPatternTransform descriptor665 (Generated.Chunk0229.pattern665) =
    orbitRepresentativePattern descriptor665.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf665 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0229.pattern665 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0229.pattern665) descriptor665 checked665 (hRep descriptor665.representative)

def descriptor666 : OrbitDescriptor := ⟨57, 10, true⟩

theorem checked666 : orbitPatternTransform descriptor666 (Generated.Chunk0229.pattern666) =
    orbitRepresentativePattern descriptor666.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf666 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0229.pattern666 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0229.pattern666) descriptor666 checked666 (hRep descriptor666.representative)

def descriptor667 : OrbitDescriptor := ⟨44, 11, true⟩

theorem checked667 : orbitPatternTransform descriptor667 (Generated.Chunk0229.pattern667) =
    orbitRepresentativePattern descriptor667.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf667 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0229.pattern667 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0229.pattern667) descriptor667 checked667 (hRep descriptor667.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0229.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0229.regionContext := by
  apply Generated.FunctionalChunk0229.valid
  · exact leaf665 hRep
  · exact leaf666 hRep
  · exact leaf667 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0229

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0230
def descriptor668 : OrbitDescriptor := ⟨47, 10, true⟩

theorem checked668 : orbitPatternTransform descriptor668 (Generated.Chunk0230.pattern668) =
    orbitRepresentativePattern descriptor668.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf668 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0230.pattern668 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0230.pattern668) descriptor668 checked668 (hRep descriptor668.representative)

def descriptor669 : OrbitDescriptor := ⟨44, 10, true⟩

theorem checked669 : orbitPatternTransform descriptor669 (Generated.Chunk0230.pattern669) =
    orbitRepresentativePattern descriptor669.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf669 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0230.pattern669 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0230.pattern669) descriptor669 checked669 (hRep descriptor669.representative)

def descriptor670 : OrbitDescriptor := ⟨41, 10, true⟩

theorem checked670 : orbitPatternTransform descriptor670 (Generated.Chunk0230.pattern670) =
    orbitRepresentativePattern descriptor670.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf670 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0230.pattern670 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0230.pattern670) descriptor670 checked670 (hRep descriptor670.representative)

def descriptor671 : OrbitDescriptor := ⟨40, 20, true⟩

theorem checked671 : orbitPatternTransform descriptor671 (Generated.Chunk0230.pattern671) =
    orbitRepresentativePattern descriptor671.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf671 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0230.pattern671 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0230.pattern671) descriptor671 checked671 (hRep descriptor671.representative)

def descriptor672 : OrbitDescriptor := ⟨38, 20, true⟩

theorem checked672 : orbitPatternTransform descriptor672 (Generated.Chunk0230.pattern672) =
    orbitRepresentativePattern descriptor672.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf672 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0230.pattern672 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0230.pattern672) descriptor672 checked672 (hRep descriptor672.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0230.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0230.regionContext := by
  apply Generated.FunctionalChunk0230.valid
  · exact leaf668 hRep
  · exact leaf669 hRep
  · exact leaf670 hRep
  · exact leaf671 hRep
  · exact leaf672 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0230

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0231
def descriptor673 : OrbitDescriptor := ⟨8, 19, false⟩

theorem checked673 : orbitPatternTransform descriptor673 (Generated.Chunk0231.pattern673) =
    orbitRepresentativePattern descriptor673.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf673 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0231.pattern673 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0231.pattern673) descriptor673 checked673 (hRep descriptor673.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0231.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0231.regionContext := by
  apply Generated.FunctionalChunk0231.valid
  · exact leaf673 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0231
