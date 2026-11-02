import MaxCaterpillar.Frontier.StarCertificate.XiQuadKappa
import MaxCaterpillar.Frontier.StarCertificate.XiCachedTargets
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

/-- Force one coefficient-dictionary lookup before evaluating its four
weights against all four output coordinates. -/
def applyIntegerQuad (direction : ℤ) (q : IntegerQuad)
    (forms : Fin 4 → IntegerForm 4) : IntegerQuad :=
  match q with
  | ⟨a,b,c,d⟩ =>
    ⟨direction*(a*forms 0 0+b*forms 1 0+c*forms 2 0+d*forms 3 0),
     direction*(a*forms 0 1+b*forms 1 1+c*forms 2 1+d*forms 3 1),
     direction*(a*forms 0 2+b*forms 1 2+c*forms 2 2+d*forms 3 2),
     direction*(a*forms 0 3+b*forms 1 3+c*forms 2 3+d*forms 3 3)⟩

theorem applyIntegerQuad_toForm (direction : ℤ) (q : IntegerQuad)
    (forms : Fin 4 → IntegerForm 4) (i : Fin 4) :
    (applyIntegerQuad direction q forms).toForm i =
      intSum 4 (fun j => (direction*q.toForm j)*forms j i) := by
  cases q
  fin_cases i <;> simp [applyIntegerQuad, IntegerQuad.toForm, intSum, Fin.succ] <;> ring_nf <;> with_unfolding_all rfl

def fastMaskedXiQuad (T : Fin 16) (p : Fin 120) (s : Fin 15 → Sign) : IntegerQuad :=
  let chainSigns := fun j => (fastMaskedChain T p j).sign s
  let orientation := headSign chainSigns
  let normalized := fun t => normalizeSign orientation ((fastMaskedCoarse T p t).sign s)
  let weights := if fastMixed chainSigns = true then fastStarIntegerKappaQuad normalized
    else (⟨10,-20,20,-10⟩ : IntegerQuad)
  applyIntegerQuad orientation.integerDirection weights
    (fun j => (fastMaskedChain T p j).integerForm starIntegerSubsetForms)

theorem fastMaskedXiQuad_toForm (T : Fin 16) (p : Fin 120) (s : Fin 15 → Sign) (i : Fin 4) :
    (fastMaskedXiQuad T p s).toForm i = fastMaskedXiIntegerCoefficients T p s i := by
  unfold fastMaskedXiQuad fastMaskedXiIntegerCoefficients
  rw [applyIntegerQuad_toForm]
  apply congrArg (intSum 4)
  funext j
  split_ifs
  · rw [congrFun (fastStarIntegerKappaQuad_toFast _) j]
  · rfl

/-- Pattern-match both inputs before constructing the sum, retaining shared
constructor evaluation across the four coordinates. -/
def forcedQuadAdd (q r : IntegerQuad) : IntegerQuad :=
  match q,r with
  | ⟨a,b,c,d⟩,⟨e,f,g,h⟩ => ⟨a+e,b+f,c+g,d+h⟩

theorem forcedQuadAdd_toForm (q r : IntegerQuad) :
    (forcedQuadAdd q r).toForm = q.toForm+r.toForm := by
  cases q; cases r
  funext i
  fin_cases i <;> rfl

def quadSum : (n : ℕ) → (Fin n → IntegerQuad) → IntegerQuad
  | 0,_ => 0
  | n+1,f => forcedQuadAdd (f 0) (quadSum n (fun i => f i.succ))

theorem quadSum_toForm (n : ℕ) (f : Fin n → IntegerQuad) (i : Fin 4) :
    (quadSum n f).toForm i = intSum n (fun j => (f j).toForm i) := by
  induction n with
  | zero => simp [quadSum,intSum]
  | succ n ih => simp only [quadSum,forcedQuadAdd_toForm,Pi.add_apply,ih,intSum]

def fastMaskedPsiQuad (T P : Fin 16) (s : Fin 15 → Sign) : IntegerQuad :=
  quadSum 120 (fun p => if fastCenterBeforeMask p = P then fastMaskedXiQuad T p s else 0)

theorem fastMaskedPsiQuad_toForm (T P : Fin 16) (s : Fin 15 → Sign) (i : Fin 4) :
    (fastMaskedPsiQuad T P s).toForm i = maskedPsiIntegerCoefficients T P s i := by
  unfold fastMaskedPsiQuad
  rw [quadSum_toForm, ← fastMaskedPsiIntegerCoefficients_eq]
  unfold fastMaskedPsiIntegerCoefficients
  apply congrArg (intSum 120)
  funext p
  split_ifs
  · exact fastMaskedXiQuad_toForm T p s i
  · simp only [IntegerQuad.toForm_zero, Pi.zero_apply]

def integerQuadTableCheck {n : ℕ} (f g : Fin n → IntegerQuad) : Bool :=
  finAll n (fun j => decide (f j = g j))

theorem integerQuadTableCheck_sound {n : ℕ} (f g : Fin n → IntegerQuad)
    (h : integerQuadTableCheck f g = true) (j : Fin n) : f j = g j :=
  of_decide_eq_true ((finAll_eq_true n _).mp h j)

end MaxCaterpillar.Frontier.StarCertificate
