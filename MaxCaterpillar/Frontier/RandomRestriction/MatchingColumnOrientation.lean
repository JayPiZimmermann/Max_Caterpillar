import MaxCaterpillar.Frontier.RandomRestriction.MatchingFiber
import MaxCaterpillar.Frontier.RandomRestriction.MatchingColumns
import MaxCaterpillar.Frontier.RandomRestriction.CoinRank

/-! # Orient actual matching columns by their actual comparison coins

The raw vector follows the current endpoint order, so swapping that pair
reverses its root. The actual comparison coin reverses simultaneously. Their
signed product is invariant under every genuine matching slot swap, hence is
constant on the actual recorded-data fiber. No sorted-label reindexing or
nonzero-weight assumption is required.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.Matching
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- The actual comparison orientation: true=+1 and false=-1. -/
def signCoin (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem signCoin_not (b : Bool) : signCoin (!b) = -signCoin b := by
  cases b <;> norm_num [signCoin]

theorem coin_difference_mul_signCoin (b : Bool) :
    (coinCoefficient (!b) - coinCoefficient b) * signCoin b = -1 := by
  cases b <;> norm_num [coinCoefficient,signCoin]

/-- The literal raw edge column at the actual current endpoint labels. -/
noncomputable def rawColumn (slot : (ι × Bool) ↪ Fin m)
    (E : Fin m → Fin m → ℝ) (tau : Equiv.Perm (Fin m)) (i : ι) : Fin m → ℝ :=
  -E (tau (slot (i,false))) (tau (slot (i,true))) •
    matchingRoot (slot.trans tau.toEmbedding) i

/-- Changing this very pair reverses the raw vector, including arbitrary real
symmetric edge weights and the zero-weight case. -/
theorem rawColumn_swap_self (slot : (ι × Bool) ↪ Fin m)
    (E : Fin m → Fin m → ℝ) (hE : ∀ a b, E a b = E b a)
    (tau : Equiv.Perm (Fin m)) (i : ι) :
    rawColumn slot E (swapTau slot i tau) i = -rawColumn slot E tau i := by
  funext x
  change (-E ((swapTau slot i tau) (slot (i,false)))
      ((swapTau slot i tau) (slot (i,true)))) *
      ((if x = (swapTau slot i tau) (slot (i,false)) then 1 else 0) -
        (if x = (swapTau slot i tau) (slot (i,true)) then 1 else 0)) =
    -((-E (tau (slot (i,false))) (tau (slot (i,true)))) *
      ((if x = tau (slot (i,false)) then 1 else 0) -
        (if x = tau (slot (i,true)) then 1 else 0)))
  rw [swapTau_left,swapTau_right,hE (tau (slot (i,true))) (tau (slot (i,false)))]
  ring

/-- Every other genuine matching swap fixes this raw column's actual endpoints. -/
theorem rawColumn_swap_other (slot : (ι × Bool) ↪ Fin m)
    (E : Fin m → Fin m → ℝ) (tau : Equiv.Perm (Fin m))
    (j i : ι) (hij : i ≠ j) :
    rawColumn slot E (swapTau slot j tau) i = rawColumn slot E tau i := by
  funext x
  change (-E ((swapTau slot j tau) (slot (i,false)))
      ((swapTau slot j tau) (slot (i,true)))) *
      ((if x = (swapTau slot j tau) (slot (i,false)) then 1 else 0) -
        (if x = (swapTau slot j tau) (slot (i,true)) then 1 else 0)) =
    (-E (tau (slot (i,false))) (tau (slot (i,true)))) *
      ((if x = tau (slot (i,false)) then 1 else 0) -
        (if x = tau (slot (i,true)) then 1 else 0))
  rw [swapTau_other slot j i hij false,swapTau_other slot j i hij true]

/-- Coin-oriented actual raw vector. -/
noncomputable def signedColumn (slot : (ι × Bool) ↪ Fin m)
    (E : Fin m → Fin m → ℝ) (tau : Equiv.Perm (Fin m)) (i : ι) : Fin m → ℝ :=
  signCoin (coins slot tau i) • rawColumn slot E tau i

/-- Both reversals cancel for the designated pair; all other swaps fix both
its comparison coin and its endpoint vector. -/
theorem signedColumn_swap (slot : (ι × Bool) ↪ Fin m)
    (E : Fin m → Fin m → ℝ) (hE : ∀ a b, E a b = E b a)
    (tau : Equiv.Perm (Fin m)) (j i : ι) :
    signedColumn slot E (swapTau slot j tau) i = signedColumn slot E tau i := by
  have hc := congrFun (coins_swapTau slot j tau) i
  unfold signedColumn
  by_cases hij : i = j
  · subst j
    simp only [flipBit,eq_self_iff_true,ite_true] at hc
    rw [hc,rawColumn_swap_self slot E hE,signCoin_not,neg_smul,smul_neg,neg_neg]
  · simp only [flipBit,if_neg hij] at hc
    rw [hc,rawColumn_swap_other slot E tau j i hij]

/-- Genuine matching flips make the coin-oriented column constant on every
actual recorded-data fiber. -/
theorem signedColumn_constant (slot : (ι × Bool) ↪ Fin m)
    (E : Fin m → Fin m → ℝ) (hE : ∀ a b, E a b = E b a)
    (u : Data ι m) (p q : Fiber slot u) (i : ι) :
    signedColumn slot E p.val i = signedColumn slot E q.val i := by
  apply invariant_constant slot u (fun p => signedColumn slot E p.val i) _ p q
  intro j r
  change signedColumn slot E (swapTau slot j r.val) i = signedColumn slot E r.val i
  exact signedColumn_swap slot E hE r.val j i

/-- The fixed actual column at any chosen member of the actual matching fiber. -/
noncomputable def canonicalColumn (slot : (ι × Bool) ↪ Fin m)
    (E : Fin m → Fin m → ℝ) {u : Data ι m} (base : Fiber slot u) (i : ι) : Fin m → ℝ :=
  signedColumn slot E base.val i

/-- The current negative raw column is exactly the Boolean affine flip
coefficient times the fixed canonical column, with the actual 0/1 convention. -/
theorem neg_rawColumn_eq_coin_difference (slot : (ι × Bool) ↪ Fin m)
    (E : Fin m → Fin m → ℝ) (hE : ∀ a b, E a b = E b a)
    (u : Data ι m) (base p : Fiber slot u) (i : ι) :
    -rawColumn slot E p.val i =
      (coinCoefficient (!(fiberCoins slot u p i)) - coinCoefficient (fiberCoins slot u p i)) •
        canonicalColumn slot E base i := by
  have h := signedColumn_constant slot E hE u p base i
  change signedColumn slot E p.val i = canonicalColumn slot E base i at h
  rw [←h]
  change -rawColumn slot E p.val i =
    (coinCoefficient (!(coins slot p.val i)) - coinCoefficient (coins slot p.val i)) •
      (signCoin (coins slot p.val i) • rawColumn slot E p.val i)
  rw [smul_smul,coin_difference_mul_signCoin,neg_one_smul]

theorem signCoin_ne_zero (b : Bool) : signCoin b ≠ 0 := by
  cases b <;> norm_num [signCoin]

/-- The fixed oriented column is an actual weighted matching root, retaining
all original endpoint labels and its full signed real coefficient. -/
theorem canonicalColumn_eq_weighted (slot : (ι × Bool) ↪ Fin m)
    (E : Fin m → Fin m → ℝ) {u : Data ι m} (base : Fiber slot u) (i : ι) :
    canonicalColumn slot E base i = weightedMatchingColumn (slot.trans base.val.toEmbedding)
      (fun j => signCoin (coins slot base.val j) *
        (-E (base.val (slot (j,false))) (base.val (slot (j,true))))) i := by
  simp only [canonicalColumn,signedColumn,rawColumn,weightedMatchingColumn,smul_smul]

/-- Every selected family of fixed fiber columns with nonzero actual edge
weights is independent, with zero weights permitted on every other edge. -/
theorem canonicalColumns_on_independent (slot : (ι × Bool) ↪ Fin m)
    (E : Fin m → Fin m → ℝ) {u : Data ι m} (base : Fiber slot u) (s : Finset ι)
    (hE : ∀ i ∈ s, E (base.val (slot (i,false))) (base.val (slot (i,true))) ≠ 0) :
    LinearIndependent ℝ (fun i : s => canonicalColumn slot E base i.val) := by
  simp_rw [canonicalColumn_eq_weighted]
  apply weightedMatchingColumns_on_independent
  intro i hi
  exact mul_ne_zero (signCoin_ne_zero _) (neg_ne_zero.mpr (hE i hi))

#print axioms rawColumn_swap_self
#print axioms rawColumn_swap_other
#print axioms signedColumn_swap
#print axioms signedColumn_constant
#print axioms neg_rawColumn_eq_coin_difference
#print axioms canonicalColumn_eq_weighted
#print axioms canonicalColumns_on_independent
end MaxCaterpillar.Frontier.RandomRestriction.Matching
