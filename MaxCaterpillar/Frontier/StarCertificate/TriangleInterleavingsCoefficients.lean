import MaxCaterpillar.Frontier.StarCertificate.TriangleInterleavingsData
import MaxCaterpillar.Frontier.StarCertificate.StarCoefficients

/-! The checked coefficients of the actual triangle quadratic along every chain. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace MaxCaterpillar.Frontier.StarCertificate.TriangleInterleavings
open BigOperators

/-- Boolean coordinates as integers, used only for exact symbolic coefficients. -/
def bit (B : Finset (Fin 5)) (i : Fin 5) : ℤ := if i ∈ B then 1 else 0

/-- Coefficients of the native quadratic: A,B,C,x01,y02,z12,u,v. -/
def nativeCoefficients (B : Finset (Fin 5)) : Fin 8 → ℤ :=
  ![bit B 0,bit B 1,bit B 2,bit B 0*bit B 1,bit B 0*bit B 2,
    bit B 1*bit B 2,bit B 3,bit B 4]

/-- Prefix sum of the increment coefficients in a fixed interleaving. -/
def prefixCoefficients (o : Fin 6) (q : Fin 20) (r : Fin 4) (j : Fin 8) : ℤ :=
  ∑ k : Fin 5, if k.val ≤ r.val then incrementCoefficients o (shuffleTable q k) j else 0

/-- Finite identities in integer polynomial coefficients. These imply the
chain identities for every real parameter vector, including all degeneracies. -/
theorem native_prefix_coefficients : ∀ (o : Fin 6) (q : Fin 20) (r : Fin 4) (j : Fin 8),
    nativeCoefficients (chamberPrefix (shuffleIndex (o,q)) r) j =
      prefixCoefficients o q r j := by decide

#print axioms native_prefix_coefficients
end MaxCaterpillar.Frontier.StarCertificate.TriangleInterleavings
