import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# A triangle extension requiring no analytic regularity

The six orders of three interacting coordinates are paired according to their
last coordinate. Their pair contribution is symmetric in the first two linear
coefficients. If the three-pair sum vanishes whenever one interaction is zero
(a star), it vanishes for every triangle.

The proof is purely algebraic. The auxiliary axis function is additive after
subtracting its value at zero; boundedness, continuity, homogeneity and
piecewise linearity are unnecessary. This file does not assert that any
particular certificate satisfies the star identity or identify a sum over
permutations with the three-pair expression.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Frontier.StarCertificate.Triangle

/-- Three paired contributions, one for each possible last coordinate. -/
def value (f : ℝ → ℝ → ℝ → ℝ) (A B C x y z : ℝ) : ℝ :=
  f A B x + f A C y + f B C z

/-- The actual restricted hypothesis: at least one of the three interactions
vanishes. The conclusion below removes this restriction. -/
def StarIdentity (f : ℝ → ℝ → ℝ → ℝ) (lam : ℝ) : Prop :=
  ∀ A B C x y z : ℝ, A + B + C + x + y + z = lam →
    (x = 0 ∨ y = 0 ∨ z = 0) → value f A B C x y z = 0

/-- The value along one coordinate axis of the zero-interaction pair. -/
def axis (f : ℝ → ℝ → ℝ → ℝ) (p : ℝ) : ℝ := f p 0 0

lemma one_edge_formula (f : ℝ → ℝ → ℝ → ℝ) (lam : ℝ)
    (hstar : StarIdentity f lam) (p q r e : ℝ)
    (htotal : p + r + q + e = lam) :
    f p q e = -f p r 0 - f r q 0 := by
  have h := hstar p r q 0 e 0 (by linarith only [htotal]) (Or.inl rfl)
  unfold value at h
  linarith only [h]

lemma zero_edge_four_point (f : ℝ → ℝ → ℝ → ℝ) (lam : ℝ)
    (hsymm : ∀ p q e, f p q e = f q p e) (hstar : StarIdentity f lam)
    (p q r s : ℝ) :
    f p s 0 + f q r 0 - f r s 0 = f p q 0 := by
  let a := lam - r - s
  have htwo := hstar a p q (r - p) (s - q) 0
    (by dsimp [a]; ring) (Or.inr (Or.inr rfl))
  have hone := one_edge_formula f lam hstar a p s (r - p)
    (by dsimp [a]; ring)
  have htwo' := one_edge_formula f lam hstar a q r (s - q)
    (by dsimp [a]; ring)
  have hmodular := hstar a r s 0 0 0
    (by dsimp [a]; ring) (Or.inl rfl)
  rw [hsymm s p 0] at hone
  rw [hsymm r q 0] at htwo'
  unfold value at htwo hmodular
  linarith only [htwo, hone, htwo', hmodular]

lemma zero_edge_eq_axis (f : ℝ → ℝ → ℝ → ℝ) (lam : ℝ)
    (hsymm : ∀ p q e, f p q e = f q p e) (hstar : StarIdentity f lam)
    (p q : ℝ) : f p q 0 = axis f p + axis f q - axis f 0 := by
  have h := zero_edge_four_point f lam hsymm hstar p q 0 0
  exact h.symm

lemma axis_modular_sum (f : ℝ → ℝ → ℝ → ℝ) (lam : ℝ)
    (hsymm : ∀ p q e, f p q e = f q p e) (hstar : StarIdentity f lam)
    (a b c : ℝ) (htotal : a + b + c = lam) :
    axis f a + axis f b + axis f c = 3 * axis f 0 / 2 := by
  have h := hstar a b c 0 0 0 (by linarith only [htotal]) (Or.inl rfl)
  unfold value at h
  rw [zero_edge_eq_axis f lam hsymm hstar a b,
    zero_edge_eq_axis f lam hsymm hstar a c,
    zero_edge_eq_axis f lam hsymm hstar b c] at h
  linarith only [h]

/-- Additivity after subtracting the value at zero, without a regularity
assumption on the axis function. -/
theorem axis_add (f : ℝ → ℝ → ℝ → ℝ) (lam : ℝ)
    (hsymm : ∀ p q e, f p q e = f q p e) (hstar : StarIdentity f lam)
    (a b : ℝ) : axis f (a + b) = axis f a + axis f b - axis f 0 := by
  have h := axis_modular_sum f lam hsymm hstar a b (lam - a - b) (by ring)
  have h' := axis_modular_sum f lam hsymm hstar (a + b) 0 (lam - a - b) (by ring)
  linarith only [h, h']

lemma axis_at_total (f : ℝ → ℝ → ℝ → ℝ) (lam : ℝ)
    (hsymm : ∀ p q e, f p q e = f q p e) (hstar : StarIdentity f lam) :
    axis f lam = -axis f 0 / 2 := by
  have h := axis_modular_sum f lam hsymm hstar 0 0 lam (by ring)
  linarith only [h]

/-- The exact finite sum needed for a triangle; no real-linearity theorem is
used to derive it from the additive identity. -/
lemma axis_six_sum (f : ℝ → ℝ → ℝ → ℝ) (lam : ℝ)
    (hsymm : ∀ p q e, f p q e = f q p e) (hstar : StarIdentity f lam)
    (a b c d e t : ℝ) (htotal : a + b + c + d + e + t = 2 * lam) :
    axis f a + axis f b + axis f c + axis f d + axis f e + axis f t =
      3 * axis f 0 := by
  have h1 := axis_add f lam hsymm hstar a b
  have h2 := axis_add f lam hsymm hstar (a + b) c
  have h3 := axis_add f lam hsymm hstar (a + b + c) d
  have h4 := axis_add f lam hsymm hstar (a + b + c + d) e
  have h5 := axis_add f lam hsymm hstar (a + b + c + d + e) t
  have hd := axis_add f lam hsymm hstar lam lam
  have hl := axis_at_total f lam hsymm hstar
  have he : axis f (a + b + c + d + e + t) = axis f (lam + lam) := by
    congr 1
    linarith only [htotal]
  linarith only [h1, h2, h3, h4, h5, hd, hl, he]

/-- Every symmetric pair functional satisfying the genuine star identities
also satisfies the unrestricted triangle identity. -/
theorem triangle_identity (f : ℝ → ℝ → ℝ → ℝ) (lam : ℝ)
    (hsymm : ∀ p q e, f p q e = f q p e) (hstar : StarIdentity f lam)
    (A B C x y z : ℝ) (htotal : A + B + C + x + y + z = lam) :
    value f A B C x y z = 0 := by
  have h1 := one_edge_formula f lam hstar A B (C + y + z) x
    (by linarith only [htotal])
  have h2 := one_edge_formula f lam hstar A C (B + x + z) y
    (by linarith only [htotal])
  have h3 := one_edge_formula f lam hstar B C (A + x + y) z
    (by linarith only [htotal])
  rw [zero_edge_eq_axis f lam hsymm hstar A (C + y + z),
    zero_edge_eq_axis f lam hsymm hstar (C + y + z) B] at h1
  rw [zero_edge_eq_axis f lam hsymm hstar A (B + x + z),
    zero_edge_eq_axis f lam hsymm hstar (B + x + z) C] at h2
  rw [zero_edge_eq_axis f lam hsymm hstar B (A + x + y),
    zero_edge_eq_axis f lam hsymm hstar (A + x + y) C] at h3
  have hsix := axis_six_sum f lam hsymm hstar A B C
    (A + x + y) (B + x + z) (C + y + z) (by linarith only [htotal])
  unfold value
  linarith only [h1, h2, h3, hsix]

/-- Pair the two orders ending at the same third coordinate, after summing
over the interleavings with the two noninteracting coordinates. -/
def interleavingPair (Ψ : ℝ → ℝ → ℝ → ℝ) (lam p q e : ℝ) : ℝ :=
  Ψ p (q + e) (lam - p - q - e) + Ψ q (p + e) (lam - p - q - e)

lemma interleavingPair_symm (Ψ : ℝ → ℝ → ℝ → ℝ) (lam p q e : ℝ) :
    interleavingPair Ψ lam p q e = interleavingPair Ψ lam q p e := by
  have he : lam - q - p - e = lam - p - q - e := by ring
  simp only [interleavingPair, he]
  ring

/-- Jensen's triangle extension at the generic interleaving-functional level.
The star hypothesis is the restricted, zero-edge identity; no assumption of
boundedness or analytic regularity is imposed on Ψ. -/
theorem interleaving_triangle_identity (Ψ : ℝ → ℝ → ℝ → ℝ) (lam : ℝ)
    (hstar : StarIdentity (interleavingPair Ψ lam) lam)
    (A B C x y z : ℝ) (htotal : A + B + C + x + y + z = lam) :
    value (interleavingPair Ψ lam) A B C x y z = 0 :=
  triangle_identity (interleavingPair Ψ lam) lam
    (interleavingPair_symm Ψ lam) hstar A B C x y z htotal

/-- The six actual orders of the interacting coordinates. This is the form
consumed by a permutation/interleaving decomposition of a certificate sum. -/
theorem six_order_identity (Ψ : ℝ → ℝ → ℝ → ℝ) (lam : ℝ)
    (hstar : StarIdentity (interleavingPair Ψ lam) lam)
    (A B C x y z : ℝ) (htotal : A + B + C + x + y + z = lam) :
    Ψ A (B + x) (C + y + z) + Ψ B (A + x) (C + y + z) +
      Ψ A (C + y) (B + x + z) + Ψ C (A + y) (B + x + z) +
      Ψ B (C + z) (A + x + y) + Ψ C (B + z) (A + x + y) = 0 := by
  have h := interleaving_triangle_identity Ψ lam hstar A B C x y z htotal
  have hC : lam - A - B - x = C + y + z := by linarith only [htotal]
  have hB : lam - A - C - y = B + x + z := by linarith only [htotal]
  have hA : lam - B - C - z = A + x + y := by linarith only [htotal]
  unfold value interleavingPair at h
  rw [hC, hB, hA] at h
  linarith only [h]

#check @triangle_identity
#check @interleaving_triangle_identity
#check @six_order_identity
#print axioms axis_add
#print axioms triangle_identity
#print axioms interleaving_triangle_identity
#print axioms six_order_identity
end MaxCaterpillar.Frontier.StarCertificate.Triangle
