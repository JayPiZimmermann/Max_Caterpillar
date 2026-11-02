import MaxCaterpillar.Frontier.RandomRestriction.CartesianInorder
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Perm

/-!
# Actual raw permutation configurations and plane Cartesian trees

The raw configuration is a pair of ordinary permutations: the tail-label
order and the gap-rank order. The anchor is an additional first leaf. This
file proves a bijection with intrinsically specified strict-heap plane trees;
the uniform orientation model is not assumed as a definition.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.Cartesian

abbrev RawConfig (m : ℕ) := Equiv.Perm (Fin m) × Equiv.Perm (Fin m)

def rawLeaves {m : ℕ} (p : RawConfig m) : List (Option (Fin m)) :=
  none :: (List.ofFn p.1).map some

def rawGaps {m : ℕ} (p : RawConfig m) : List (Fin m) := List.ofFn p.2

def rawWordOfConfig {m : ℕ} (p : RawConfig m) : RawWord (Option (Fin m)) (Fin m) where
  leaves := rawLeaves p
  gaps := rawGaps p
  length_eq := by simp [rawLeaves, rawGaps]
  gaps_nodup := List.nodup_ofFn_ofInjective p.2.injective

/-- Intrinsic list conditions: the anchor is first, each tail label occurs
once, and every gap rank occurs. Gap distinctness is already in RawWord. -/
def IsAnchored (m : ℕ) (w : RawWord (Option (Fin m)) (Fin m)) : Prop :=
  ∃ tail : List (Fin m), w.leaves = none :: tail.map some ∧ tail.Nodup ∧
    (∀ a : Fin m, a ∈ tail) ∧ (∀ a : Fin m, a ∈ w.gaps)

def AnchoredWord (m : ℕ) := {w : RawWord (Option (Fin m)) (Fin m) // IsAnchored m w}

def PlaneConfig (m : ℕ) :=
  {t : HeapTree (α := Option (Fin m)) (β := Fin m) // IsAnchored m (serialize t)}

lemma ofFn_perm_complete {m : ℕ} (p : Equiv.Perm (Fin m)) (a : Fin m) :
    a ∈ List.ofFn p :=
  (List.mem_ofFn p a).mpr (p.surjective a)

lemma rawWordOfConfig_anchored {m : ℕ} (p : RawConfig m) :
    IsAnchored m (rawWordOfConfig p) := by
  refine ⟨List.ofFn p.1, rfl, List.nodup_ofFn_ofInjective p.1.injective, ?_, ?_⟩
  · exact ofFn_perm_complete p.1
  · exact ofFn_perm_complete p.2

def encodeRaw {m : ℕ} (p : RawConfig m) : AnchoredWord m :=
  ⟨rawWordOfConfig p, rawWordOfConfig_anchored p⟩

lemma complete_word_length {m : ℕ} (l : List (Fin m)) (hnd : l.Nodup)
    (hall : ∀ a : Fin m, a ∈ l) : l.length = m := by
  have h := Fintype.card_congr (List.Nodup.getEquivOfForallMemList l hnd hall)
  simpa only [Fintype.card_fin] using h

/-- Recover the actual permutation whose word is l, using its actual list
indexing equivalence, not a separate orientation parameterization. -/
noncomputable def permOfWord {m : ℕ} (l : List (Fin m)) (hnd : l.Nodup)
    (hall : ∀ a : Fin m, a ∈ l) : Equiv.Perm (Fin m) :=
  (finCongr (complete_word_length l hnd hall).symm).trans
    (List.Nodup.getEquivOfForallMemList l hnd hall)

lemma ofFn_permOfWord {m : ℕ} (l : List (Fin m)) (hnd : l.Nodup)
    (hall : ∀ a : Fin m, a ∈ l) : List.ofFn (permOfWord l hnd hall) = l := by
  change List.ofFn (fun i : Fin m => l.get
    (Fin.cast (complete_word_length l hnd hall).symm i)) = l
  exact (List.ofFn_congr (complete_word_length l hnd hall) l.get).symm.trans (List.ofFn_get l)

lemma rawWord_ext {α β : Type*} (w w' : RawWord α β)
    (hl : w.leaves = w'.leaves) (hg : w.gaps = w'.gaps) : w = w' := by
  cases w
  cases w'
  cases hl
  cases hg
  rfl

theorem encodeRaw_bijective (m : ℕ) : Function.Bijective (encodeRaw (m := m)) := by
  constructor
  · intro p q he
    have hw := congrArg Subtype.val he
    have hl := congrArg RawWord.leaves hw
    have hg := congrArg RawWord.gaps hw
    have ht : List.ofFn p.1 = List.ofFn q.1 := by
      apply (List.map_injective_iff.mpr (Option.some_injective (Fin m)))
      exact List.cons.inj hl |>.2
    have hp : p.1 = q.1 := Equiv.ext (fun i => congrFun (List.ofFn_injective ht) i)
    have hq : p.2 = q.2 := Equiv.ext (fun i => congrFun (List.ofFn_injective hg) i)
    exact Prod.ext hp hq
  · intro w
    rcases w.property with ⟨tail, hl, hnd, hall, hgap⟩
    let tau := permOfWord tail hnd hall
    let rho := permOfWord w.val.gaps w.val.gaps_nodup hgap
    refine ⟨(tau, rho), ?_⟩
    apply Subtype.ext
    apply rawWord_ext
    · change none :: (List.ofFn tau).map some = w.val.leaves
      rw [ofFn_permOfWord]
      exact hl.symm
    · exact ofFn_permOfWord w.val.gaps w.val.gaps_nodup hgap

noncomputable def rawAnchoredWordEquiv (m : ℕ) : RawConfig m ≃ AnchoredWord m :=
  Equiv.ofBijective encodeRaw (encodeRaw_bijective m)

noncomputable def planeAnchoredWordEquiv (m : ℕ) : PlaneConfig m ≃ AnchoredWord m :=
  heapTreeRawWordEquiv.subtypeEquiv (fun _ => Iff.rfl)

/-- The actual pair (tau,rho) is in bijection with the anchored plane
Cartesian tree. Uniform raw counting therefore transports bijectively. -/
noncomputable def rawPlaneEquiv (m : ℕ) : RawConfig m ≃ PlaneConfig m :=
  (rawAnchoredWordEquiv m).trans (planeAnchoredWordEquiv m).symm

theorem rawPlaneEquiv_leaves (m : ℕ) (p : RawConfig m) :
    inorderLeaves (rawPlaneEquiv m p).val.val = rawLeaves p :=
  congrArg (fun w : AnchoredWord m => w.val.leaves)
    ((planeAnchoredWordEquiv m).apply_symm_apply (rawAnchoredWordEquiv m p))

theorem rawPlaneEquiv_gaps (m : ℕ) (p : RawConfig m) :
    inorderGaps (rawPlaneEquiv m p).val.val = rawGaps p :=
  congrArg (fun w : AnchoredWord m => w.val.gaps)
    ((planeAnchoredWordEquiv m).apply_symm_apply (rawAnchoredWordEquiv m p))

theorem raw_config_card (m : ℕ) : Fintype.card (RawConfig m) = (Nat.factorial m) ^ 2 := by
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
  ring

noncomputable instance planeConfigFintype (m : ℕ) : Fintype (PlaneConfig m) :=
  Fintype.ofEquiv (RawConfig m) (rawPlaneEquiv m)

theorem plane_config_card (m : ℕ) : Fintype.card (PlaneConfig m) = (Nat.factorial m) ^ 2 := by
  exact (Fintype.card_congr (rawPlaneEquiv m)).symm.trans (raw_config_card m)

#check @rawPlaneEquiv
#check @rawPlaneEquiv_leaves
#check @rawPlaneEquiv_gaps
#check @raw_config_card
#check @plane_config_card
#print axioms rawPlaneEquiv
#print axioms rawPlaneEquiv_leaves
#print axioms rawPlaneEquiv_gaps
#print axioms plane_config_card
end MaxCaterpillar.Frontier.RandomRestriction.Cartesian
