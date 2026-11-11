import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0128
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0129
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0130
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0131
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0132
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0133
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0134
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0135
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0128
def descriptor356 : OrbitDescriptor := ⟨38, 12, false⟩

theorem checked356 : orbitPatternTransform descriptor356 (Generated.Chunk0128.pattern356) =
    orbitRepresentativePattern descriptor356.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf356 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0128.pattern356 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0128.pattern356) descriptor356 checked356 (hRep descriptor356.representative)

def descriptor357 : OrbitDescriptor := ⟨40, 12, false⟩

theorem checked357 : orbitPatternTransform descriptor357 (Generated.Chunk0128.pattern357) =
    orbitRepresentativePattern descriptor357.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf357 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0128.pattern357 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0128.pattern357) descriptor357 checked357 (hRep descriptor357.representative)

def descriptor358 : OrbitDescriptor := ⟨41, 2, false⟩

theorem checked358 : orbitPatternTransform descriptor358 (Generated.Chunk0128.pattern358) =
    orbitRepresentativePattern descriptor358.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf358 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0128.pattern358 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0128.pattern358) descriptor358 checked358 (hRep descriptor358.representative)

def descriptor359 : OrbitDescriptor := ⟨44, 2, false⟩

theorem checked359 : orbitPatternTransform descriptor359 (Generated.Chunk0128.pattern359) =
    orbitRepresentativePattern descriptor359.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf359 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0128.pattern359 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0128.pattern359) descriptor359 checked359 (hRep descriptor359.representative)

def descriptor360 : OrbitDescriptor := ⟨47, 2, false⟩

theorem checked360 : orbitPatternTransform descriptor360 (Generated.Chunk0128.pattern360) =
    orbitRepresentativePattern descriptor360.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf360 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0128.pattern360 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0128.pattern360) descriptor360 checked360 (hRep descriptor360.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0128.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0128.regionContext := by
  apply Generated.FunctionalChunk0128.valid
  · exact leaf356 hRep
  · exact leaf357 hRep
  · exact leaf358 hRep
  · exact leaf359 hRep
  · exact leaf360 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0128

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0129
def descriptor361 : OrbitDescriptor := ⟨42, 12, false⟩

theorem checked361 : orbitPatternTransform descriptor361 (Generated.Chunk0129.pattern361) =
    orbitRepresentativePattern descriptor361.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf361 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0129.pattern361 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0129.pattern361) descriptor361 checked361 (hRep descriptor361.representative)

def descriptor362 : OrbitDescriptor := ⟨43, 12, false⟩

theorem checked362 : orbitPatternTransform descriptor362 (Generated.Chunk0129.pattern362) =
    orbitRepresentativePattern descriptor362.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf362 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0129.pattern362 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0129.pattern362) descriptor362 checked362 (hRep descriptor362.representative)

def descriptor363 : OrbitDescriptor := ⟨44, 12, false⟩

theorem checked363 : orbitPatternTransform descriptor363 (Generated.Chunk0129.pattern363) =
    orbitRepresentativePattern descriptor363.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf363 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0129.pattern363 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0129.pattern363) descriptor363 checked363 (hRep descriptor363.representative)

def descriptor364 : OrbitDescriptor := ⟨48, 2, false⟩

theorem checked364 : orbitPatternTransform descriptor364 (Generated.Chunk0129.pattern364) =
    orbitRepresentativePattern descriptor364.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf364 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0129.pattern364 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0129.pattern364) descriptor364 checked364 (hRep descriptor364.representative)

def descriptor365 : OrbitDescriptor := ⟨49, 2, false⟩

theorem checked365 : orbitPatternTransform descriptor365 (Generated.Chunk0129.pattern365) =
    orbitRepresentativePattern descriptor365.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf365 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0129.pattern365 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0129.pattern365) descriptor365 checked365 (hRep descriptor365.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0129.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0129.regionContext := by
  apply Generated.FunctionalChunk0129.valid
  · exact leaf361 hRep
  · exact leaf362 hRep
  · exact leaf363 hRep
  · exact leaf364 hRep
  · exact leaf365 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0129

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0130
def descriptor366 : OrbitDescriptor := ⟨45, 12, false⟩

theorem checked366 : orbitPatternTransform descriptor366 (Generated.Chunk0130.pattern366) =
    orbitRepresentativePattern descriptor366.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf366 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0130.pattern366 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0130.pattern366) descriptor366 checked366 (hRep descriptor366.representative)

def descriptor367 : OrbitDescriptor := ⟨46, 12, false⟩

theorem checked367 : orbitPatternTransform descriptor367 (Generated.Chunk0130.pattern367) =
    orbitRepresentativePattern descriptor367.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf367 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0130.pattern367 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0130.pattern367) descriptor367 checked367 (hRep descriptor367.representative)

def descriptor368 : OrbitDescriptor := ⟨47, 12, false⟩

theorem checked368 : orbitPatternTransform descriptor368 (Generated.Chunk0130.pattern368) =
    orbitRepresentativePattern descriptor368.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf368 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0130.pattern368 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0130.pattern368) descriptor368 checked368 (hRep descriptor368.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0130.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0130.regionContext := by
  apply Generated.FunctionalChunk0130.valid
  · exact leaf366 hRep
  · exact leaf367 hRep
  · exact leaf368 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0130

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0131
def descriptor369 : OrbitDescriptor := ⟨49, 12, false⟩

theorem checked369 : orbitPatternTransform descriptor369 (Generated.Chunk0131.pattern369) =
    orbitRepresentativePattern descriptor369.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf369 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0131.pattern369 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0131.pattern369) descriptor369 checked369 (hRep descriptor369.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0131.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0131.regionContext := by
  apply Generated.FunctionalChunk0131.valid
  · exact leaf369 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0131

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0132
def descriptor370 : OrbitDescriptor := ⟨50, 2, false⟩

theorem checked370 : orbitPatternTransform descriptor370 (Generated.Chunk0132.pattern370) =
    orbitRepresentativePattern descriptor370.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf370 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0132.pattern370 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0132.pattern370) descriptor370 checked370 (hRep descriptor370.representative)

def descriptor371 : OrbitDescriptor := ⟨51, 2, false⟩

theorem checked371 : orbitPatternTransform descriptor371 (Generated.Chunk0132.pattern371) =
    orbitRepresentativePattern descriptor371.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf371 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0132.pattern371 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0132.pattern371) descriptor371 checked371 (hRep descriptor371.representative)

def descriptor372 : OrbitDescriptor := ⟨52, 2, false⟩

theorem checked372 : orbitPatternTransform descriptor372 (Generated.Chunk0132.pattern372) =
    orbitRepresentativePattern descriptor372.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf372 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0132.pattern372 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0132.pattern372) descriptor372 checked372 (hRep descriptor372.representative)

def descriptor373 : OrbitDescriptor := ⟨53, 2, false⟩

theorem checked373 : orbitPatternTransform descriptor373 (Generated.Chunk0132.pattern373) =
    orbitRepresentativePattern descriptor373.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf373 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0132.pattern373 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0132.pattern373) descriptor373 checked373 (hRep descriptor373.representative)

def descriptor374 : OrbitDescriptor := ⟨54, 2, false⟩

theorem checked374 : orbitPatternTransform descriptor374 (Generated.Chunk0132.pattern374) =
    orbitRepresentativePattern descriptor374.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf374 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0132.pattern374 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0132.pattern374) descriptor374 checked374 (hRep descriptor374.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0132.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0132.regionContext := by
  apply Generated.FunctionalChunk0132.valid
  · exact leaf370 hRep
  · exact leaf371 hRep
  · exact leaf372 hRep
  · exact leaf373 hRep
  · exact leaf374 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0132

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0133
def descriptor375 : OrbitDescriptor := ⟨3, 5, false⟩

theorem checked375 : orbitPatternTransform descriptor375 (Generated.Chunk0133.pattern375) =
    orbitRepresentativePattern descriptor375.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf375 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0133.pattern375 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0133.pattern375) descriptor375 checked375 (hRep descriptor375.representative)

def descriptor376 : OrbitDescriptor := ⟨5, 3, false⟩

theorem checked376 : orbitPatternTransform descriptor376 (Generated.Chunk0133.pattern376) =
    orbitRepresentativePattern descriptor376.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf376 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0133.pattern376 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0133.pattern376) descriptor376 checked376 (hRep descriptor376.representative)

def descriptor377 : OrbitDescriptor := ⟨6, 3, false⟩

theorem checked377 : orbitPatternTransform descriptor377 (Generated.Chunk0133.pattern377) =
    orbitRepresentativePattern descriptor377.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf377 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0133.pattern377 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0133.pattern377) descriptor377 checked377 (hRep descriptor377.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0133.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0133.regionContext := by
  apply Generated.FunctionalChunk0133.valid
  · exact leaf375 hRep
  · exact leaf376 hRep
  · exact leaf377 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0133

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0134
def descriptor378 : OrbitDescriptor := ⟨29, 3, false⟩

theorem checked378 : orbitPatternTransform descriptor378 (Generated.Chunk0134.pattern378) =
    orbitRepresentativePattern descriptor378.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf378 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0134.pattern378 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0134.pattern378) descriptor378 checked378 (hRep descriptor378.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0134.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0134.regionContext := by
  apply Generated.FunctionalChunk0134.valid
  · exact leaf378 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0134

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0135
def descriptor379 : OrbitDescriptor := ⟨42, 3, false⟩

theorem checked379 : orbitPatternTransform descriptor379 (Generated.Chunk0135.pattern379) =
    orbitRepresentativePattern descriptor379.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf379 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0135.pattern379 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0135.pattern379) descriptor379 checked379 (hRep descriptor379.representative)

def descriptor380 : OrbitDescriptor := ⟨55, 2, false⟩

theorem checked380 : orbitPatternTransform descriptor380 (Generated.Chunk0135.pattern380) =
    orbitRepresentativePattern descriptor380.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf380 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0135.pattern380 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0135.pattern380) descriptor380 checked380 (hRep descriptor380.representative)

def descriptor381 : OrbitDescriptor := ⟨58, 2, false⟩

theorem checked381 : orbitPatternTransform descriptor381 (Generated.Chunk0135.pattern381) =
    orbitRepresentativePattern descriptor381.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf381 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0135.pattern381 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0135.pattern381) descriptor381 checked381 (hRep descriptor381.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0135.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0135.regionContext := by
  apply Generated.FunctionalChunk0135.valid
  · exact leaf379 hRep
  · exact leaf380 hRep
  · exact leaf381 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0135
