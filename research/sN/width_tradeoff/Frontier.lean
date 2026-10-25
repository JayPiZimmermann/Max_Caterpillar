import MaxCaterpillar.Frontier.Main

set_option autoImplicit false

/-!
Exact formulations of the width-pair question for ordinary networks, with
arbitrary real parameters and biases and no skip connections. These lemmas
make no assertion that the unresolved maximum-of-five frontier is rectangular.
-/

namespace MaxCaterpillar.WidthTradeoff

variable {N : ℕ} {f : Point N → ℝ}

/-- Exact representation on every real input, with both widths counted. -/
def Feasible (f : Point N → ℝ) (a b : ℕ) : Prop :=
  ∃ net : Network N a b, ∀ x, net.eval x = f x

/-- A single attained pair minimizes both coordinates over all networks. -/
def LeastPair (f : Point N → ℝ) (a b : ℕ) : Prop :=
  Feasible f a b ∧ ∀ c d, Feasible f c d → a ≤ c ∧ b ≤ d

/-- Two attained widths force a genuine drop in the optimal second width.
The missing southwest corner is essential: incomparable upper bounds alone
are not a tradeoff. -/
def StrictTradeoff (f : Point N → ℝ) : Prop :=
  ∃ a b c d, Feasible f a b ∧ Feasible f c d ∧
    a < c ∧ d < b ∧ ¬ Feasible f a d

theorem feasible_mono {a b c d : ℕ} (h : Feasible f a b)
    (hac : a ≤ c) (hbd : b ≤ d) : Feasible f c d := by
  obtain ⟨net, he⟩ := h
  exact Frontier.exists_network_of_le net he hac hbd

theorem leastPair_iff_rectangle {a b : ℕ} :
    LeastPair f a b ↔ ∀ c d, Feasible f c d ↔ a ≤ c ∧ b ≤ d := by
  constructor
  · rintro ⟨hab, hmin⟩ c d
    exact ⟨hmin c d, fun h => feasible_mono hab h.1 h.2⟩
  · intro h
    exact ⟨(h a b).2 ⟨le_rfl, le_rfl⟩, fun c d => (h c d).1⟩

/-- Both separate minima are attained, possibly by different networks. -/
theorem coordinate_minima (hex : ∃ a b, Feasible f a b) :
    ∃ a b c d, Feasible f a b ∧ Feasible f c d ∧
      ∀ p q, Feasible f p q → a ≤ p ∧ d ≤ q := by
  classical
  let a := Nat.find hex
  obtain ⟨b, hab⟩ := Nat.find_spec hex
  have hex' : ∃ d c, Feasible f c d := by
    obtain ⟨p, q, hpq⟩ := hex
    exact ⟨q, p, hpq⟩
  let d := Nat.find hex'
  obtain ⟨c, hcd⟩ := Nat.find_spec hex'
  refine ⟨a, b, c, d, hab, hcd, ?_⟩
  intro p q hpq
  exact ⟨Nat.find_min' hex ⟨q, hpq⟩, Nat.find_min' hex' ⟨p, hpq⟩⟩

/-- Either both separate minima occur in one network, or there is an
attained strict tradeoff, not merely a comparison of upper bounds. -/
theorem leastPair_or_strictTradeoff (hex : ∃ a b, Feasible f a b) :
    (∃ a b, LeastPair f a b) ∨ StrictTradeoff f := by
  classical
  obtain ⟨a, b, c, d, hab, hcd, hmin⟩ := coordinate_minima hex
  by_cases had : Feasible f a d
  · exact Or.inl ⟨a, d, had, hmin⟩
  · right
    have hac := (hmin c d hcd).1
    have hdb := (hmin a b hab).2
    have hneac : a ≠ c := by
      intro he
      apply had
      simpa [he] using hcd
    have hnedb : d ≠ b := by
      intro he
      apply had
      simpa [he] using hab
    exact ⟨a, b, c, d, hab, hcd,
      lt_of_le_of_ne hac hneac, lt_of_le_of_ne hdb hnedb, had⟩

theorem strictTradeoff_not_leastPair (ht : StrictTradeoff f) :
    ¬ ∃ a b, LeastPair f a b := by
  obtain ⟨a, b, c, d, hab, hcd, _, _, hmissing⟩ := ht
  rintro ⟨p, q, hpq, hleast⟩
  exact hmissing (feasible_mono hpq (hleast a b hab).1 (hleast c d hcd).2)

theorem strictTradeoff_iff_no_leastPair (hex : ∃ a b, Feasible f a b) :
    StrictTradeoff f ↔ ¬ ∃ a b, LeastPair f a b := by
  refine ⟨strictTradeoff_not_leastPair, ?_⟩
  intro h
  exact (leastPair_or_strictTradeoff hex).resolve_left h

/-- Once a network attaining the globally smallest second width is
available, increasing the first width cannot improve that minimum. -/
theorem eventual_constant_second_width (hex : ∃ a b, Feasible f a b) :
    ∃ c d, Feasible f c d ∧
      (∀ a b, Feasible f a b → d ≤ b) ∧
      ∀ a, c ≤ a → ∀ b, Feasible f a b ↔ d ≤ b := by
  obtain ⟨_, _, c, d, _, hcd, hmin⟩ := coordinate_minima hex
  refine ⟨c, d, hcd, fun a b hab => (hmin a b hab).2, ?_⟩
  intro a hca b
  exact ⟨fun hab => (hmin a b hab).2, fun hdb => feasible_mono hcd hca hdb⟩

/-- A feasible pair that cannot be reduced in either coordinate without
increasing the other. This is weaker than being a least pair. -/
def ParetoPair (f : Point N → ℝ) (a b : ℕ) : Prop :=
  Feasible f a b ∧ ∀ c d, c ≤ a → d ≤ b → Feasible f c d → c = a ∧ d = b

/-- Every feasible pair dominates an attained Pareto-minimal pair. -/
theorem pareto_below {a b : ℕ} (hab : Feasible f a b) :
    ∃ c d, c ≤ a ∧ d ≤ b ∧ ParetoPair f c d := by
  classical
  have hex : ∃ s, ∃ c d, c ≤ a ∧ d ≤ b ∧ Feasible f c d ∧ c + d = s :=
    ⟨a + b, a, b, le_rfl, le_rfl, hab, rfl⟩
  obtain ⟨c, d, hca, hdb, hcd, hsum⟩ := Nat.find_spec hex
  refine ⟨c, d, hca, hdb, hcd, ?_⟩
  intro p q hpc hqd hpq
  have hs := Nat.find_min' hex
    (show ∃ i j, i ≤ a ∧ j ≤ b ∧ Feasible f i j ∧ i + j = p + q from
      ⟨p, q, le_trans hpc hca, le_trans hqd hdb, hpq, rfl⟩)
  constructor <;> omega

/-- All Pareto pairs lie in a finite rectangle determined by two networks
attaining the separate coordinate minima. -/
theorem pareto_bounded (hex : ∃ a b, Feasible f a b) :
    ∃ c b, ∀ p q, ParetoPair f p q → p ≤ c ∧ q ≤ b := by
  obtain ⟨a, b, c, d, hab, hcd, hmin⟩ := coordinate_minima hex
  refine ⟨c, b, ?_⟩
  intro p q hpq
  have ham := hmin p q hpq.1
  constructor
  · by_contra h
    have hcp : c ≤ p := by omega
    have he := (hpq.2 c d hcp ham.2 hcd).1
    omega
  · by_contra h
    have hbq : b ≤ q := by omega
    have he := (hpq.2 a b ham.1 hbq hab).2
    omega

theorem maximum_three_leastPair : LeastPair (Maximum 3) 4 3 := by
  apply leastPair_iff_rectangle.mpr
  intro c d
  exact Frontier.max3_widths_iff

theorem maximum_four_leastPair : LeastPair (Maximum 4) 6 3 := by
  apply leastPair_iff_rectangle.mpr
  intro c d
  exact Frontier.max4_widths_iff

#print axioms leastPair_iff_rectangle
#print axioms coordinate_minima
#print axioms strictTradeoff_iff_no_leastPair
#print axioms eventual_constant_second_width
#print axioms pareto_below
#print axioms pareto_bounded
#print axioms maximum_three_leastPair
#print axioms maximum_four_leastPair

end MaxCaterpillar.WidthTradeoff
