import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0264
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0265
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0266
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0267
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0268
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0269
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0270
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0271
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0264
def descriptor764 : OrbitDescriptor := ⟨29, 9, true⟩

theorem checked764 : orbitPatternTransform descriptor764 (Generated.Chunk0264.pattern764) =
    orbitRepresentativePattern descriptor764.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf764 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0264.pattern764 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0264.pattern764) descriptor764 checked764 (hRep descriptor764.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0264.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0264.regionContext := by
  apply Generated.FunctionalChunk0264.valid
  · exact leaf764 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0264

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0265
def descriptor765 : OrbitDescriptor := ⟨6, 9, true⟩

theorem checked765 : orbitPatternTransform descriptor765 (Generated.Chunk0265.pattern765) =
    orbitRepresentativePattern descriptor765.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf765 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0265.pattern765 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0265.pattern765) descriptor765 checked765 (hRep descriptor765.representative)

def descriptor766 : OrbitDescriptor := ⟨5, 9, true⟩

theorem checked766 : orbitPatternTransform descriptor766 (Generated.Chunk0265.pattern766) =
    orbitRepresentativePattern descriptor766.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf766 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0265.pattern766 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0265.pattern766) descriptor766 checked766 (hRep descriptor766.representative)

def descriptor767 : OrbitDescriptor := ⟨3, 11, true⟩

theorem checked767 : orbitPatternTransform descriptor767 (Generated.Chunk0265.pattern767) =
    orbitRepresentativePattern descriptor767.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf767 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0265.pattern767 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0265.pattern767) descriptor767 checked767 (hRep descriptor767.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0265.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0265.regionContext := by
  apply Generated.FunctionalChunk0265.valid
  · exact leaf765 hRep
  · exact leaf766 hRep
  · exact leaf767 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0265

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0266
def descriptor768 : OrbitDescriptor := ⟨54, 8, true⟩

theorem checked768 : orbitPatternTransform descriptor768 (Generated.Chunk0266.pattern768) =
    orbitRepresentativePattern descriptor768.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf768 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0266.pattern768 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0266.pattern768) descriptor768 checked768 (hRep descriptor768.representative)

def descriptor769 : OrbitDescriptor := ⟨53, 8, true⟩

theorem checked769 : orbitPatternTransform descriptor769 (Generated.Chunk0266.pattern769) =
    orbitRepresentativePattern descriptor769.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf769 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0266.pattern769 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0266.pattern769) descriptor769 checked769 (hRep descriptor769.representative)

def descriptor770 : OrbitDescriptor := ⟨52, 8, true⟩

theorem checked770 : orbitPatternTransform descriptor770 (Generated.Chunk0266.pattern770) =
    orbitRepresentativePattern descriptor770.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf770 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0266.pattern770 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0266.pattern770) descriptor770 checked770 (hRep descriptor770.representative)

def descriptor771 : OrbitDescriptor := ⟨51, 8, true⟩

theorem checked771 : orbitPatternTransform descriptor771 (Generated.Chunk0266.pattern771) =
    orbitRepresentativePattern descriptor771.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf771 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0266.pattern771 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0266.pattern771) descriptor771 checked771 (hRep descriptor771.representative)

def descriptor772 : OrbitDescriptor := ⟨50, 8, true⟩

theorem checked772 : orbitPatternTransform descriptor772 (Generated.Chunk0266.pattern772) =
    orbitRepresentativePattern descriptor772.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf772 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0266.pattern772 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0266.pattern772) descriptor772 checked772 (hRep descriptor772.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0266.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0266.regionContext := by
  apply Generated.FunctionalChunk0266.valid
  · exact leaf768 hRep
  · exact leaf769 hRep
  · exact leaf770 hRep
  · exact leaf771 hRep
  · exact leaf772 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0266

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0267
def descriptor773 : OrbitDescriptor := ⟨49, 14, true⟩

theorem checked773 : orbitPatternTransform descriptor773 (Generated.Chunk0267.pattern773) =
    orbitRepresentativePattern descriptor773.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf773 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0267.pattern773 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0267.pattern773) descriptor773 checked773 (hRep descriptor773.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0267.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0267.regionContext := by
  apply Generated.FunctionalChunk0267.valid
  · exact leaf773 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0267

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0268
def descriptor774 : OrbitDescriptor := ⟨47, 14, true⟩

theorem checked774 : orbitPatternTransform descriptor774 (Generated.Chunk0268.pattern774) =
    orbitRepresentativePattern descriptor774.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf774 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0268.pattern774 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0268.pattern774) descriptor774 checked774 (hRep descriptor774.representative)

def descriptor775 : OrbitDescriptor := ⟨46, 14, true⟩

theorem checked775 : orbitPatternTransform descriptor775 (Generated.Chunk0268.pattern775) =
    orbitRepresentativePattern descriptor775.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf775 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0268.pattern775 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0268.pattern775) descriptor775 checked775 (hRep descriptor775.representative)

def descriptor776 : OrbitDescriptor := ⟨45, 14, true⟩

theorem checked776 : orbitPatternTransform descriptor776 (Generated.Chunk0268.pattern776) =
    orbitRepresentativePattern descriptor776.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf776 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0268.pattern776 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0268.pattern776) descriptor776 checked776 (hRep descriptor776.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0268.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0268.regionContext := by
  apply Generated.FunctionalChunk0268.valid
  · exact leaf774 hRep
  · exact leaf775 hRep
  · exact leaf776 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0268

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0269
def descriptor777 : OrbitDescriptor := ⟨49, 8, true⟩

theorem checked777 : orbitPatternTransform descriptor777 (Generated.Chunk0269.pattern777) =
    orbitRepresentativePattern descriptor777.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf777 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0269.pattern777 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0269.pattern777) descriptor777 checked777 (hRep descriptor777.representative)

def descriptor778 : OrbitDescriptor := ⟨48, 8, true⟩

theorem checked778 : orbitPatternTransform descriptor778 (Generated.Chunk0269.pattern778) =
    orbitRepresentativePattern descriptor778.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf778 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0269.pattern778 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0269.pattern778) descriptor778 checked778 (hRep descriptor778.representative)

def descriptor779 : OrbitDescriptor := ⟨44, 14, true⟩

theorem checked779 : orbitPatternTransform descriptor779 (Generated.Chunk0269.pattern779) =
    orbitRepresentativePattern descriptor779.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf779 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0269.pattern779 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0269.pattern779) descriptor779 checked779 (hRep descriptor779.representative)

def descriptor780 : OrbitDescriptor := ⟨43, 14, true⟩

theorem checked780 : orbitPatternTransform descriptor780 (Generated.Chunk0269.pattern780) =
    orbitRepresentativePattern descriptor780.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf780 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0269.pattern780 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0269.pattern780) descriptor780 checked780 (hRep descriptor780.representative)

def descriptor781 : OrbitDescriptor := ⟨42, 14, true⟩

theorem checked781 : orbitPatternTransform descriptor781 (Generated.Chunk0269.pattern781) =
    orbitRepresentativePattern descriptor781.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf781 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0269.pattern781 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0269.pattern781) descriptor781 checked781 (hRep descriptor781.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0269.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0269.regionContext := by
  apply Generated.FunctionalChunk0269.valid
  · exact leaf777 hRep
  · exact leaf778 hRep
  · exact leaf779 hRep
  · exact leaf780 hRep
  · exact leaf781 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0269

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0270
def descriptor782 : OrbitDescriptor := ⟨47, 8, true⟩

theorem checked782 : orbitPatternTransform descriptor782 (Generated.Chunk0270.pattern782) =
    orbitRepresentativePattern descriptor782.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf782 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0270.pattern782 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0270.pattern782) descriptor782 checked782 (hRep descriptor782.representative)

def descriptor783 : OrbitDescriptor := ⟨44, 8, true⟩

theorem checked783 : orbitPatternTransform descriptor783 (Generated.Chunk0270.pattern783) =
    orbitRepresentativePattern descriptor783.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf783 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0270.pattern783 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0270.pattern783) descriptor783 checked783 (hRep descriptor783.representative)

def descriptor784 : OrbitDescriptor := ⟨41, 8, true⟩

theorem checked784 : orbitPatternTransform descriptor784 (Generated.Chunk0270.pattern784) =
    orbitRepresentativePattern descriptor784.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf784 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0270.pattern784 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0270.pattern784) descriptor784 checked784 (hRep descriptor784.representative)

def descriptor785 : OrbitDescriptor := ⟨40, 14, true⟩

theorem checked785 : orbitPatternTransform descriptor785 (Generated.Chunk0270.pattern785) =
    orbitRepresentativePattern descriptor785.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf785 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0270.pattern785 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0270.pattern785) descriptor785 checked785 (hRep descriptor785.representative)

def descriptor786 : OrbitDescriptor := ⟨38, 14, true⟩

theorem checked786 : orbitPatternTransform descriptor786 (Generated.Chunk0270.pattern786) =
    orbitRepresentativePattern descriptor786.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf786 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0270.pattern786 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0270.pattern786) descriptor786 checked786 (hRep descriptor786.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0270.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0270.regionContext := by
  apply Generated.FunctionalChunk0270.valid
  · exact leaf782 hRep
  · exact leaf783 hRep
  · exact leaf784 hRep
  · exact leaf785 hRep
  · exact leaf786 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0270

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0271
def descriptor787 : OrbitDescriptor := ⟨46, 8, true⟩

theorem checked787 : orbitPatternTransform descriptor787 (Generated.Chunk0271.pattern787) =
    orbitRepresentativePattern descriptor787.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf787 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0271.pattern787 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0271.pattern787) descriptor787 checked787 (hRep descriptor787.representative)

def descriptor788 : OrbitDescriptor := ⟨43, 8, true⟩

theorem checked788 : orbitPatternTransform descriptor788 (Generated.Chunk0271.pattern788) =
    orbitRepresentativePattern descriptor788.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf788 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0271.pattern788 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0271.pattern788) descriptor788 checked788 (hRep descriptor788.representative)

def descriptor789 : OrbitDescriptor := ⟨40, 8, true⟩

theorem checked789 : orbitPatternTransform descriptor789 (Generated.Chunk0271.pattern789) =
    orbitRepresentativePattern descriptor789.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf789 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0271.pattern789 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0271.pattern789) descriptor789 checked789 (hRep descriptor789.representative)

def descriptor790 : OrbitDescriptor := ⟨39, 8, true⟩

theorem checked790 : orbitPatternTransform descriptor790 (Generated.Chunk0271.pattern790) =
    orbitRepresentativePattern descriptor790.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf790 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0271.pattern790 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0271.pattern790) descriptor790 checked790 (hRep descriptor790.representative)

def descriptor791 : OrbitDescriptor := ⟨37, 14, true⟩

theorem checked791 : orbitPatternTransform descriptor791 (Generated.Chunk0271.pattern791) =
    orbitRepresentativePattern descriptor791.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf791 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0271.pattern791 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0271.pattern791) descriptor791 checked791 (hRep descriptor791.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0271.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0271.regionContext := by
  apply Generated.FunctionalChunk0271.valid
  · exact leaf787 hRep
  · exact leaf788 hRep
  · exact leaf789 hRep
  · exact leaf790 hRep
  · exact leaf791 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0271
