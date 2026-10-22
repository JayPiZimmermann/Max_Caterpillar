import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith

/-! # Orders with two prescribed chains

Abstract combinatorics for the cubic lower bound on `s_N`
(`research/sN/NOTE.md`, "Cubic claim C", step 3): the arms of a stretch are
forced chains, and the number of total orders of an `m`-set in which two
disjoint chains of lengths `a` and `b` appear in prescribed order is at most
`m!/(a! b!)`.

A total order of the finite type `V` is a bijection `e : V ≃ Fin (card V)`
(`e v` is the position of `v`).  A chain is an embedding `x : Fin a ↪ V`; it
appears in prescribed order when `i ↦ e (x i)` is strictly increasing.  (A
decreasing chain is obtained by precomposing with `Fin.revPerm`.)

Proof: `Perm (Fin a) × Perm (Fin b)` acts on orders by permuting the two
chains; distinct (valid order, σ, τ) give distinct orders, because two valid
orders in the same orbit agree on each chain (`Fin.strictMono_unique`) and off
the chains.
-/

open Finset Function Equiv Nat

namespace MaxCaterpillar.CountCubic

variable {V : Type*} [Fintype V] [DecidableEq V] {a b : ℕ}

/-- The permutation of `V` that moves the chain `x` by `σ` and the chain `y`
by `τ`, fixing everything else. -/
noncomputable def chainPerm (x : Fin a ↪ V) (y : Fin b ↪ V) (σ : Perm (Fin a))
    (τ : Perm (Fin b)) : Perm V :=
  σ.viaEmbedding x * τ.viaEmbedding y

section chainPerm

variable (x : Fin a ↪ V) (y : Fin b ↪ V) (σ : Perm (Fin a)) (τ : Perm (Fin b))

theorem chainPerm_apply_x (hxy : Disjoint (Set.range x) (Set.range y)) (i : Fin a) :
    chainPerm x y σ τ (x i) = x (σ i) := by
  simp only [chainPerm, Perm.mul_apply]
  rw [Perm.viaEmbedding_apply_of_not_mem _ _ _
      (fun h => Set.disjoint_left.1 hxy ⟨i, rfl⟩ h), Perm.viaEmbedding_apply]

theorem chainPerm_apply_y (hxy : Disjoint (Set.range x) (Set.range y)) (i : Fin b) :
    chainPerm x y σ τ (y i) = y (τ i) := by
  simp only [chainPerm, Perm.mul_apply]
  rw [Perm.viaEmbedding_apply, Perm.viaEmbedding_apply_of_not_mem _ _ _
      (fun h => Set.disjoint_left.1 hxy h ⟨τ i, rfl⟩)]

theorem chainPerm_apply_other (v : V) (hx : v ∉ Set.range x) (hy : v ∉ Set.range y) :
    chainPerm x y σ τ v = v := by
  simp only [chainPerm, Perm.mul_apply]
  rw [Perm.viaEmbedding_apply_of_not_mem _ _ _ hy, Perm.viaEmbedding_apply_of_not_mem _ _ _ hx]

end chainPerm

/-- The order `e` lists both chains `x` and `y` in increasing position. -/
def ChainsOrdered {n : ℕ} (x : Fin a ↪ V) (y : Fin b ↪ V) (e : V ≃ Fin n) : Prop :=
  StrictMono (fun i => e (x i)) ∧ StrictMono (fun i => e (y i))

/-- Two orders that list a chain increasingly and differ by a permutation
preserving the chain's range agree on the chain. -/
theorem chain_eq_of_strictMono {n c : ℕ} (x : Fin c ↪ V) (e₁ e₂ : V ≃ Fin n)
    (π₁ π₂ : Perm V) (σ₁ σ₂ : Perm (Fin c))
    (h₁ : ∀ i, π₁ (x i) = x (σ₁ i)) (h₂ : ∀ i, π₂ (x i) = x (σ₂ i))
    (heq : ∀ v, e₁ (π₁ v) = e₂ (π₂ v))
    (hm₁ : StrictMono (fun i => e₁ (x i))) (hm₂ : StrictMono (fun i => e₂ (x i))) :
    (fun i => e₁ (x i)) = (fun i => e₂ (x i)) := by
  apply Fin.strictMono_unique hm₁ hm₂
  have r1 : Set.range (fun i => e₁ (x i)) = Set.range (fun i => e₁ (x (σ₁ i))) :=
    (EquivLike.range_comp (fun i => e₁ (x i)) σ₁).symm
  have r2 : Set.range (fun i => e₂ (x i)) = Set.range (fun i => e₂ (x (σ₂ i))) :=
    (EquivLike.range_comp (fun i => e₂ (x i)) σ₂).symm
  rw [r1, r2]
  exact congrArg Set.range (funext fun i => by rw [← h₁, ← h₂, heq])

/-- **Two-chain count.** The number of total orders of `V` (`m = card V`) in
which the disjoint chains `x` (length `a`) and `y` (length `b`) both appear in
increasing order satisfies `count * a! * b! ≤ m!`. -/
theorem card_chainsOrdered_mul_le (x : Fin a ↪ V) (y : Fin b ↪ V)
    (hxy : Disjoint (Set.range x) (Set.range y)) [DecidablePred
      (ChainsOrdered (n := Fintype.card V) x y)] :
    (univ.filter (ChainsOrdered (n := Fintype.card V) x y)).card * a ! * b ! ≤
      (Fintype.card V)! := by
  set A := univ.filter (ChainsOrdered (n := Fintype.card V) x y)
  let F : (V ≃ Fin (Fintype.card V)) × Perm (Fin a) × Perm (Fin b) →
      (V ≃ Fin (Fintype.card V)) := fun p => (chainPerm x y p.2.1 p.2.2).trans p.1
  have hcard : (A ×ˢ ((univ : Finset (Perm (Fin a))) ×ˢ (univ : Finset (Perm (Fin b))))).card
      = A.card * a ! * b ! := by
    rw [card_product, card_product, card_univ, card_univ, Fintype.card_perm,
      Fintype.card_perm, Fintype.card_fin, Fintype.card_fin, mul_assoc]
  rw [← hcard]
  have huniv : (univ : Finset (V ≃ Fin (Fintype.card V))).card = (Fintype.card V)! := by
    rw [card_univ, Fintype.card_equiv (Fintype.equivFin V)]
  rw [← huniv]
  refine card_le_card_of_inj_on F (fun _ _ => mem_univ _) ?_
  rintro ⟨e₁, σ₁, τ₁⟩ h₁ ⟨e₂, σ₂, τ₂⟩ h₂ hF
  simp only [mem_product, mem_filter, mem_univ, true_and, and_true] at h₁ h₂
  have heq : ∀ v, e₁ (chainPerm x y σ₁ τ₁ v) = e₂ (chainPerm x y σ₂ τ₂ v) := by
    intro v
    have := congrArg (fun f : V ≃ Fin (Fintype.card V) => f v) hF
    simpa [F] using this
  have hx := chain_eq_of_strictMono x e₁ e₂ _ _ σ₁ σ₂
    (chainPerm_apply_x x y σ₁ τ₁ hxy) (chainPerm_apply_x x y σ₂ τ₂ hxy) heq h₁.1 h₂.1
  have hy := chain_eq_of_strictMono y e₁ e₂ _ _ τ₁ τ₂
    (chainPerm_apply_y x y σ₁ τ₁ hxy) (chainPerm_apply_y x y σ₂ τ₂ hxy) heq h₁.2 h₂.2
  have he : e₁ = e₂ := by
    ext v
    by_cases hvx : v ∈ Set.range x
    · obtain ⟨i, rfl⟩ := hvx
      exact congrArg Fin.val (congrFun hx i)
    by_cases hvy : v ∈ Set.range y
    · obtain ⟨i, rfl⟩ := hvy
      exact congrArg Fin.val (congrFun hy i)
    have := heq v
    rw [chainPerm_apply_other x y σ₁ τ₁ v hvx hvy,
      chainPerm_apply_other x y σ₂ τ₂ v hvx hvy] at this
    rw [this]
  subst he
  have hπ : ∀ v, chainPerm x y σ₁ τ₁ v = chainPerm x y σ₂ τ₂ v :=
    fun v => e₁.injective (heq v)
  have hσ : σ₁ = σ₂ := by
    ext i
    have := hπ (x i)
    rw [chainPerm_apply_x x y σ₁ τ₁ hxy, chainPerm_apply_x x y σ₂ τ₂ hxy] at this
    rw [x.injective this]
  have hτ : τ₁ = τ₂ := by
    ext i
    have := hπ (y i)
    rw [chainPerm_apply_y x y σ₁ τ₁ hxy, chainPerm_apply_y x y σ₂ τ₂ hxy] at this
    rw [y.injective this]
  rw [hσ, hτ]

/-- Probability form: a uniformly random total order of `V` lists both chains
increasingly with probability at most `1/(a! b!)`. -/
theorem card_chainsOrdered_div_le (x : Fin a ↪ V) (y : Fin b ↪ V)
    (hxy : Disjoint (Set.range x) (Set.range y)) [DecidablePred
      (ChainsOrdered (n := Fintype.card V) x y)] :
    ((univ.filter (ChainsOrdered (n := Fintype.card V) x y)).card : ℚ) /
        ((Fintype.card V)! : ℚ) ≤ 1 / ((a ! : ℚ) * (b ! : ℚ)) := by
  have h := card_chainsOrdered_mul_le x y hxy
  have hpos : (0 : ℚ) < ((Fintype.card V)! : ℚ) := by exact_mod_cast factorial_pos _
  rw [div_le_div_iff hpos (by positivity), one_mul]
  have : (((univ.filter (ChainsOrdered (n := Fintype.card V) x y)).card * a ! * b ! : ℕ) : ℚ)
      ≤ ((Fintype.card V)! : ℚ) := by exact_mod_cast h
  push_cast at this
  rw [← mul_assoc]
  exact this

end MaxCaterpillar.CountCubic
