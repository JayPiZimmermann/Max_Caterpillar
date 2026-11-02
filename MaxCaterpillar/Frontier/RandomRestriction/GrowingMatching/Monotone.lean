import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Structural

/-! # Upward input-arity monotonicity of the actual local obstruction

The proof uses literal generic localization, not graph contraction. No
counting, probability or additional structural hypothesis is introduced.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
open NormalizedNetwork DominantGap Cartesian
attribute [local instance] Classical.propDecidable

/-- An actual obstruction at k₀ selected inputs remains an obstruction at
every larger input arity. Positive q guarantees the returned original outer
neuron survives the actual localization. -/
theorem localMatchingObstruction_mono_arity {k₀ n q : ℕ} [NeZero k₀] [NeZero n]
    (H : LocalMatchingObstruction k₀ q) (hkn : k₀≤n) (hq : 0<q) :
    LocalMatchingObstruction n q := by
  classical
  intro h₁ h₂ model hn hs hmax
  let f : Fin k₀ ↪ Fin n := prefixEmbedding hkn
  let S : Finset (Fin n) := Finset.univ.image f
  let e := complementEmbedding S
  have hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin n)) \ Finset.univ.image f :=
    complementEmbedding_image S
  have hno : ∀ j,3≤(rowSupport (model.A j)).card →
      ¬rowSupport (model.A j)⊆Finset.univ.image f := by
    intro j hlarge _
    exact (Nat.not_succ_le_self 2) (le_trans hlarge (hs j))
  obtain ⟨B,_hB,hthreshold⟩ := exists_structural_witness_threshold H hq model hn hmax f e hcomp
  let p : RawConfig ((Finset.univ : Finset (Fin n)) \ S).card :=
    (Equiv.refl _,Equiv.refl _)
  obtain ⟨r,_hr,C,hC,_hselected⟩ := hthreshold B (le_refl B) p hno
  exact ⟨r,C,hC,Finset.subset_univ _⟩

#print axioms localMatchingObstruction_mono_arity
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
