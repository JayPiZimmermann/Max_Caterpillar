import MaxCaterpillar.Frontier.RandomRestriction.MatchingCoins

/-!
# Local matching data and its coins determine the actual permutation

The data keep every unordered paired label and every unmatched label. The
comparison coin specifies the order of each paired label. Therefore no extra
unrecorded state remains on a fixed-data, fixed-coin fiber.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.Matching

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

lemma ordered_pair_recover {α : Type*} [LinearOrder α] (a b c d : α)
    (hab : a ≠ b) (hset : ∀ x, (x = a ∨ x = b) ↔ (x = c ∨ x = d))
    (hcoin : a < b ↔ c < d) : a = c ∧ b = d := by
  have ha : a = c ∨ a = d := (hset a).mp (Or.inl rfl)
  have hb : b = c ∨ b = d := (hset b).mp (Or.inr rfl)
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · exact False.elim (hab (ha.trans hb.symm))
    · exact ⟨ha, hb⟩
  · rcases hb with hb | hb
    · rw [← ha, ← hb] at hcoin
      by_cases hlt : a < b
      · have hnot : ¬b < a := not_lt_of_ge (le_of_lt hlt)
        exact False.elim (hnot (hcoin.mp hlt))
      · have hgt : b < a := lt_of_le_of_ne (le_of_not_gt hlt) (fun he => hab he.symm)
        exact False.elim (hlt (hcoin.mpr hgt))
    · exact False.elim (hab (ha.trans hb.symm))

/-- The actual permutation is separated by recorded matching data and coins. -/
theorem recorded_coins_injective (slot : (ι × Bool) ↪ Fin m)
    (tau tau' : Equiv.Perm (Fin m))
    (hdata : recorded slot tau = recorded slot tau')
    (hcoins : coins slot tau = coins slot tau') : tau = tau' := by
  have hpairs := congrArg Prod.fst hdata
  have houtside := congrArg Prod.snd hdata
  apply Equiv.ext
  intro p
  by_cases hp : p ∈ usedPositions slot
  · obtain ⟨⟨i, b⟩, _, he⟩ := Finset.mem_image.mp hp
    subst p
    have hne : tau (slot (i, false)) ≠ tau (slot (i, true)) :=
      fun h => slot_pair_ne slot i (tau.injective h)
    have hset : ∀ x, (x = tau (slot (i, false)) ∨ x = tau (slot (i, true))) ↔
        (x = tau' (slot (i, false)) ∨ x = tau' (slot (i, true))) := by
      intro x
      have h : x ∈ pairLabels slot tau i ↔ x ∈ pairLabels slot tau' i :=
        Finset.ext_iff.mp (congrFun hpairs i) x
      simpa only [pairLabels, Finset.mem_insert, Finset.mem_singleton] using h
    have hcoin : tau (slot (i, false)) < tau (slot (i, true)) ↔
        tau' (slot (i, false)) < tau' (slot (i, true)) := by
      have h := congrArg (fun b : Bool => b = true) (congrFun hcoins i)
      exact Iff.of_eq (by simpa [coins] using h)
    have hpair := ordered_pair_recover (tau (slot (i, false))) (tau (slot (i, true)))
      (tau' (slot (i, false))) (tau' (slot (i, true))) hne
      hset hcoin
    cases b
    · exact hpair.1
    · exact hpair.2
  · have h := congrFun houtside p
    change (if p ∈ usedPositions slot then none else some (tau p)) =
      (if p ∈ usedPositions slot then none else some (tau' p)) at h
    rw [if_neg hp, if_neg hp] at h
    exact Option.some.inj h

def Fiber (slot : (ι × Bool) ↪ Fin m) (u : Data ι m) :=
  {tau : Equiv.Perm (Fin m) // recorded slot tau = u}

noncomputable instance fiberFintype (slot : (ι × Bool) ↪ Fin m) (u : Data ι m) :
    Fintype (Fiber slot u) := by
  classical
  unfold Fiber
  infer_instance

def fiberCoins (slot : (ι × Bool) ↪ Fin m) (u : Data ι m) (p : Fiber slot u) : ι → Bool :=
  coins slot p.val

def fiberFlip (slot : (ι × Bool) ↪ Fin m) (u : Data ι m) (i : ι) :
    Fiber slot u ≃ Fiber slot u :=
  (swapTauEquiv slot i).subtypeEquiv (fun tau => by
    change recorded slot tau = u ↔ recorded slot (swapTau slot i tau) = u
    rw [recorded_swapTau])

theorem fiberCoins_injective (slot : (ι × Bool) ↪ Fin m) (u : Data ι m) :
    Function.Injective (fiberCoins slot u) := by
  intro p q hcoins
  apply Subtype.ext
  exact recorded_coins_injective slot p.val q.val (p.property.trans q.property.symm) hcoins

theorem fiberCoins_flip (slot : (ι × Bool) ↪ Fin m) (u : Data ι m) (i : ι) (p : Fiber slot u) :
    fiberCoins slot u (fiberFlip slot u i p) = flipBit i (fiberCoins slot u p) :=
  coins_swapTau slot i p.val

/-- A flip-invariant value is constant on the actual local-data fiber.
This derives the orbit statement from genuine flips and coin separation. -/
theorem invariant_constant (slot : (ι × Bool) ↪ Fin m) (u : Data ι m)
    {A : Type*} (F : Fiber slot u → A)
    (hflip : ∀ i p, F (fiberFlip slot u i p) = F p)
    (p q : Fiber slot u) : F p = F q := by
  classical
  let system : CoinFlipSystem F (fiberCoins slot u) :=
    ⟨fiberFlip slot u, hflip, fiberCoins_flip slot u⟩
  have hc := coin_pattern_cards_equal F (fiberCoins slot u) system (F p)
    (fiberCoins slot u p) (fiberCoins slot u q)
  have hp : p ∈ patternFiber F (fiberCoins slot u) (F p) (fiberCoins slot u p) := by
    simp only [mem_patternFiber, and_self, eq_self_iff_true]
  have hpos : 0 < (patternFiber F (fiberCoins slot u) (F p) (fiberCoins slot u q)).card := by
    rw [← hc]
    exact Finset.card_pos.mpr ⟨p, hp⟩
  obtain ⟨r, hr⟩ := Finset.card_pos.mp hpos
  rcases (mem_patternFiber _ _ _ _ _).mp hr with ⟨hF, hcoins⟩
  have hrq : r = q := fiberCoins_injective slot u hcoins
  exact hF.symm.trans (congrArg F hrq)

#check @recorded_coins_injective
#check @fiberCoins_injective
#check @invariant_constant
#print axioms recorded_coins_injective
#print axioms fiberCoins_injective
#print axioms invariant_constant
end MaxCaterpillar.Frontier.RandomRestriction.Matching
