import MaxCaterpillar.Frontier.StarCertificate.XiCompiledSelectors
import MaxCaterpillar.Frontier.StarCertificate.XiQuadEval
import MaxCaterpillar.Frontier.StarCertificate.XiPermutationGroups
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

/-- One row match exposes all references and all coefficient quads before
normalization or arithmetic begins. -/
def evalCompiledXiQuad (row : CompiledSelectorRow) (s : Fin 15 → Sign) : IntegerQuad :=
  match row with
  | ⟨chain,coarse,coefficients⟩ =>
    let chainSigns := fun j => (chain j).sign s
    let orientation := headSign chainSigns
    let normalized := fun t => normalizeSign orientation ((coarse t).sign s)
    let weights := if fastMixed chainSigns = true then fastStarIntegerKappaQuad normalized
      else (⟨10,-20,20,-10⟩ : IntegerQuad)
    applyIntegerQuad orientation.integerDirection weights (fun j => (coefficients j).toForm)

def compiledMaskedXiQuad (T : Fin 16) (p : Fin 120) (s : Fin 15 → Sign) : IntegerQuad :=
  evalCompiledXiQuad (compiledSelectorRow T p) s

theorem compiledMaskedXiQuad_eq (T : Fin 16) (p : Fin 120) (s : Fin 15 → Sign) :
    compiledMaskedXiQuad T p s = fastMaskedXiQuad T p s := by
  cases hr : compiledSelectorRow T p with
  | mk chain coarse coefficients =>
    have hc : chain = fastMaskedChain T p := by
      funext j
      rw [fastMaskedChain_eq]
      simpa only [hr] using compiledSelectorRow_chain T p j
    have hh : coarse = fastMaskedCoarse T p := by
      funext j
      rw [fastMaskedCoarse_eq]
      simpa only [hr] using compiledSelectorRow_coarse T p j
    have hf : (fun j => (coefficients j).toForm) =
        fun j => (fastMaskedChain T p j).integerForm starIntegerSubsetForms := by
      funext j i
      rw [fastMaskedChain_eq]
      simpa only [hr] using compiledSelectorRow_coefficients T p j i
    unfold compiledMaskedXiQuad
    rw [hr]
    dsimp only [evalCompiledXiQuad]
    unfold fastMaskedXiQuad
    rw [hc, hh, hf]

def listForcedQuadSum : List (Fin 120) → (Fin 120 → IntegerQuad) → IntegerQuad
  | [],_ => 0
  | p::ps,f => forcedQuadAdd (f p) (listForcedQuadSum ps f)

theorem listForcedQuadSum_toForm (ps : List (Fin 120)) (f : Fin 120 → IntegerQuad) (i : Fin 4) :
    (listForcedQuadSum ps f).toForm i = (ps.map (fun p => (f p).toForm i)).sum := by
  induction ps with
  | nil => simp [listForcedQuadSum]
  | cons p ps ih =>
    simp only [listForcedQuadSum,forcedQuadAdd_toForm,Pi.add_apply,List.map_cons,List.sum_cons,ih]

/-- The per-P lists contain exactly 120 total entries over all P. This
avoids 1920 filter scans and avoids deeply nested Fin.succ loop indices. -/
def compiledMaskedPsiQuad (T P : Fin 16) (s : Fin 15 → Sign) : IntegerQuad :=
  listForcedQuadSum (permutationsBeforeMask P) (fun p => compiledMaskedXiQuad T p s)

theorem compiledMaskedPsiQuad_toForm (T P : Fin 16) (s : Fin 15 → Sign) (i : Fin 4) :
    (compiledMaskedPsiQuad T P s).toForm i = maskedPsiIntegerCoefficients T P s i := by
  unfold compiledMaskedPsiQuad
  rw [listForcedQuadSum_toForm, sum_permutationsBeforeMask, ← fastMaskedPsiIntegerCoefficients_eq]
  unfold fastMaskedPsiIntegerCoefficients
  rw [intSum_eq_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : fastCenterBeforeMask p = P
  · simp only [if_pos hp, compiledMaskedXiQuad_eq, fastMaskedXiQuad_toForm]
  · simp only [if_neg hp]

end MaxCaterpillar.Frontier.StarCertificate
