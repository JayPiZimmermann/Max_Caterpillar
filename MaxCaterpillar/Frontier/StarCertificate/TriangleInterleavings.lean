import MaxCaterpillar.Frontier.StarCertificate.TriangleInterleavingsCoefficients
import MaxCaterpillar.Frontier.StarCertificate.StarPermutations
import MaxCaterpillar.Frontier.StarCertificate.Triangle

/-!
# Actual triangle chains are the six interleaving sums

The native set function is a quadratic polynomial in Boolean coordinates,
with arbitrary real coefficients. Its actual 120 permutation chains are
reindexed as six orders of the interacting coordinates and twenty shuffles
with the two modular coordinates. The Xi function is completely arbitrary.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace MaxCaterpillar.Frontier.StarCertificate.TriangleInterleavings
open BigOperators

/-- The primitive fixed-012 triangle polynomial; coefficient order is
A,B,C,x01,y02,z12,u,v. -/
noncomputable def nativeTriangle (p : Fin 8 → ℝ) (B : Finset (Fin 5)) : ℝ :=
  ∑ j, (nativeCoefficients B j : ℝ) * p j

/-- Actual chain values of a modular gradient in one of the twenty shuffles. -/
noncomputable def modularChain (w : Fin 5 → ℝ) (q : Fin 20) : Fin 4 → ℝ :=
  fun r => ∑ k : Fin 5, if k.val ≤ r.val then w (shuffleTable q k) else 0

/-- Sum over every interleaving with the two fixed modular coordinates. -/
noncomputable def interleavingPsi (Xi : (Fin 4 → ℝ) → ℝ) (u v X Y Z : ℝ) : ℝ :=
  ∑ q : Fin 20, Xi (modularChain ![X,Y,Z,u,v] q)

/-- Actual linear increments of the triangle in each of its six orders. -/
noncomputable def increments (p : Fin 8 → ℝ) (o : Fin 6) : Fin 5 → ℝ :=
  fun i => ∑ j, (incrementCoefficients o i j : ℝ) * p j

/-- Integer coefficient equality gives the actual chain identity over all reals. -/
theorem native_chain_interleaving (p : Fin 8 → ℝ) (o : Fin 6) (q : Fin 20) :
    permutationFunctionChain (nativeTriangle p) (permutationEquiv (shuffleIndex (o,q))) =
      modularChain (increments p o) q := by
  funext r
  change (∑ j, (nativeCoefficients (chamberPrefix (shuffleIndex (o,q)) r) j : ℝ) * p j) =
    ∑ k : Fin 5, if k.val ≤ r.val then
      (∑ j, (incrementCoefficients o (shuffleTable q k) j : ℝ) * p j) else 0
  simp_rw [native_prefix_coefficients]
  simp only [prefixCoefficients,Int.cast_sum,apply_ite,Int.cast_zero]
  simp_rw [Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.val ≤ r.val
  · simp only [if_pos hk]
  · simp only [if_neg hk,Finset.sum_const_zero]

/-- All six ordered gradients, with independent modular coordinates 3 and 4. -/
theorem increments_explicit (p : Fin 8 → ℝ) :
    increments p =
      ![![p 0,p 1+p 3,p 2+p 4+p 5,p 6,p 7],
        ![p 1,p 0+p 3,p 2+p 4+p 5,p 6,p 7],
        ![p 0,p 2+p 4,p 1+p 3+p 5,p 6,p 7],
        ![p 2,p 0+p 4,p 1+p 3+p 5,p 6,p 7],
        ![p 1,p 2+p 5,p 0+p 3+p 4,p 6,p 7],
        ![p 2,p 1+p 5,p 0+p 3+p 4,p 6,p 7]] := by
  funext o i
  fin_cases o <;> fin_cases i <;>
    norm_num [increments,incrementCoefficients,Fin.sum_univ_succ] <;> ring_nf <;> rfl

noncomputable def shuffleEquiv : (Fin 6 × Fin 20) ≃ Fin 120 :=
  Equiv.ofBijective shuffleIndex shuffleIndex_bijective

/-- A codomain-independent reindexing: every actual permutation occurs once. -/
theorem sum_shuffles {R : Type*} [AddCommMonoid R] (f : Fin 120 → R) :
    (∑ p : Fin 120,f p) = ∑ o : Fin 6,∑ q : Fin 20,f (shuffleIndex (o,q)) := by
  calc
    _ = ∑ p : Fin 6 × Fin 20,f (shuffleIndex p) :=
      (Fintype.sum_equiv shuffleEquiv
        (fun p : Fin 6 × Fin 20 => f (shuffleIndex p)) f (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type

/-- The actual permutation sum of a native triangle equals the six ordered
interleaving sums. No total-zero or certificate property is used here. -/
theorem sum_native_triangle_interleavings (Xi : (Fin 4 → ℝ) → ℝ)
    (A B C x y z u v : ℝ) :
    (∑ pi : Equiv.Perm (Fin 5), Xi (permutationFunctionChain
      (nativeTriangle ![A,B,C,x,y,z,u,v]) pi)) =
      interleavingPsi Xi u v A (B+x) (C+y+z) +
      interleavingPsi Xi u v B (A+x) (C+y+z) +
      interleavingPsi Xi u v A (C+y) (B+x+z) +
      interleavingPsi Xi u v C (A+y) (B+x+z) +
      interleavingPsi Xi u v B (C+z) (A+x+y) +
      interleavingPsi Xi u v C (B+z) (A+x+y) := by
  rw [←sum_permutationTable,sum_shuffles]
  simp_rw [native_chain_interleaving,increments_explicit]
  rw [Fin.sum_univ_six]
  rfl

/-- Any all-real zero-edge triangle identity extends to every native triangle.
The hypothesis refers to actual permutation chains, not an abstract pairing. -/
theorem native_triangle_sum_zero_of_zero_edge
    (Xi : (Fin 4 → ℝ) → ℝ) (u v : ℝ)
    (hstar : ∀ A B C x y z : ℝ,
      A+B+C+x+y+z+u+v=0 → (x=0 ∨ y=0 ∨ z=0) →
      (∑ pi : Equiv.Perm (Fin 5), Xi (permutationFunctionChain
        (nativeTriangle ![A,B,C,x,y,z,u,v]) pi))=0)
    (A B C x y z : ℝ) (htotal : A+B+C+x+y+z+u+v=0) :
    (∑ pi : Equiv.Perm (Fin 5), Xi (permutationFunctionChain
      (nativeTriangle ![A,B,C,x,y,z,u,v]) pi))=0 := by
  let Ψ := interleavingPsi Xi u v
  have hs : Triangle.StarIdentity (Triangle.interleavingPair Ψ (-u-v)) (-u-v) := by
    intro a b c d e f hsum hzero
    have hz := hstar a b c d e f (by linarith only [hsum]) hzero
    rw [sum_native_triangle_interleavings] at hz
    unfold Triangle.value Triangle.interleavingPair
    change Ψ a (b+d) (-u-v-a-b-d) + Ψ b (a+d) (-u-v-a-b-d) +
      (Ψ a (c+e) (-u-v-a-c-e) + Ψ c (a+e) (-u-v-a-c-e)) +
      (Ψ b (c+f) (-u-v-b-c-f) + Ψ c (b+f) (-u-v-b-c-f)) = 0
    have h1 : -u-v-a-b-d=c+e+f := by linarith only [hsum]
    have h2 : -u-v-a-c-e=b+d+f := by linarith only [hsum]
    have h3 : -u-v-b-c-f=a+d+e := by linarith only [hsum]
    rw [h1,h2,h3]
    dsimp only [Ψ] at *
    linarith only [hz]
  rw [sum_native_triangle_interleavings]
  exact Triangle.six_order_identity Ψ (-u-v) hs A B C x y z
    (by linarith only [htotal])

#check @sum_native_triangle_interleavings
#check @native_triangle_sum_zero_of_zero_edge
#print axioms native_chain_interleaving
#print axioms sum_native_triangle_interleavings
#print axioms native_triangle_sum_zero_of_zero_edge
end MaxCaterpillar.Frontier.StarCertificate.TriangleInterleavings
