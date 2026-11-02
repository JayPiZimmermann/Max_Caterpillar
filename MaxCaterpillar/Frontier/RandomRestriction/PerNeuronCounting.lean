import MaxCaterpillar.Frontier.RandomRestriction.PerNeuronTail

/-! # Actual graph, tail, and outer-event averaging

The only input left explicit in this intermediate theorem is the actual
conditional rank bound. Every permutation count and the constant 400 are
derived here from the concrete events and the actual matching estimate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace MaxCaterpillar.Frontier.RandomRestriction.PerNeuron
open BigOperators Configurations GoodEvent DominantGap
variable {m h₁ h₂ : ℕ}
attribute [local instance] braidGraphDecidable

theorem neuron_event_card_le_of_clean_fiber_bounds
    (net : NormalizedNetwork (m+5) h₁ h₂) (hn : net.TranslationNormalized)
    (K : ℕ) (T : ℝ) (k : Fin h₂)
    (hm : 400≤m) (hKlow : 4≤K) (hKhigh : (K:ℝ)≤(m:ℝ)/100)
    (hrank : ∀ σ : FullPerm m, ∀ ρ : RankPerm m,
      ∀ u : Matching.Data (↥(rankIsolatedGaps ρ K)) m,
      ∀ base : Matching.Fiber (rankIsolatedSlots ρ K) u,
      ActualClean net (baseTail σ) k ρ K base.val →
      ((Finset.univ.filter fun p : Matching.Fiber (rankIsolatedSlots ρ K) u =>
        net.inner k (actualGapPoint (baseTail σ) (p.val,ρ) T)=0).card : ℝ) /
          Fintype.card (Matching.Fiber (rankIsolatedSlots ρ K) u) ≤
        (1/2:ℝ)^nativeMatchingCount
          ((braidInteractionGraph net hn k).comap (baseTail σ))
          (rankIsolatedSlots ρ K) base.val) :
    K^2*(neuronEvent net hn K T k).card ≤ 400*Fintype.card (Configuration m) := by
  classical
  let G := braidInteractionGraph net hn k
  let η : ℝ := G.edgeFinset.card
  let density : ℝ := 60*η^2/(m:ℝ)^4
  let bound : ℝ := 400/(K:ℝ)^2
  have hm0 : 0<m := lt_of_lt_of_le (by norm_num) hm
  have hmR : 400≤(m:ℝ) := by exact_mod_cast hm
  have hKpos : (0:ℝ)<K := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hKlow : 0<K)
  have hdensity : 0≤density := by dsimp only [density]; positivity
  have hbound : 0≤bound := by dsimp only [bound]; positivity
  have hselected : ((GraphRestriction.twoEdgesEvent G).card:ℝ) ≤
      density*Fintype.card (FullPerm m) := by
    have hh := GraphRestriction.twoEdgesEvent_fraction_le_tail G hm0
    have hc : (0:ℝ)<Fintype.card (FullPerm m) := by exact_mod_cast Fintype.card_pos
    exact (div_le_iff hc).mp hh
  have hmain : ((neuronEvent net hn K T k).card:ℝ) ≤
      bound*Fintype.card (Configuration m) := by
    apply outer_density_event_card_le (GraphRestriction.twoEdgesEvent G)
      (neuronEvent net hn K T k) density bound hdensity hbound hselected
    · intro σ ρ τ hω
      exact (GraphRestriction.mem_twoEdgesEvent G σ).mpr
        ((mem_neuronEvent net hn K T k (σ,τ,ρ)).mp hω).2.2.2
    · intro σ hσ ρ
      by_cases hρ : ρ∈badIsolatedEvent m K
      · have hempty : tailFiber (neuronEvent net hn K T k) σ ρ=∅ := by
          apply Finset.eq_empty_iff_forall_not_mem.mpr
          intro τ hτ
          exact ((mem_neuronEvent net hn K T k (σ,τ,ρ)).mp
            ((mem_tailFiber _ σ ρ τ).mp hτ)).2.1 hρ
        rw [hempty,Finset.card_empty,Nat.cast_zero,mul_zero]
        positivity
      · have hJ : (K:ℝ)/2≤Fintype.card (↥(rankIsolatedGaps ρ K)) := by
          have hh := not_lt.mp (fun h => hρ ((mem_badIsolatedEvent ρ).mpr h))
          simpa only [Fintype.card_coe,rankIsolatedGaps] using hh
        have htail := neuron_tail_card_le_of_clean_fiber_bound net hn K T k σ ρ (hrank σ ρ)
        have hmatch := native_matching_counting_le_four_hundred
          (G.comap (baseTail σ)) (rankIsolatedSlots ρ K) (K:ℝ) η hmR hKpos hKhigh
          (Nat.cast_nonneg _) hJ (tail_braidGraph_edge_lower_bound net hn k σ)
        have hCP : (0:ℝ)<Fintype.card (TailPerm m) := by exact_mod_cast Fintype.card_pos
        calc
          density*((tailFiber (neuronEvent net hn K T k) σ ρ).card:ℝ) ≤
              density*∑ τ : TailPerm m,(1/2:ℝ)^nativeMatchingCount
                (G.comap (baseTail σ)) (rankIsolatedSlots ρ K) τ :=
            mul_le_mul_of_nonneg_left htail hdensity
          _ = (density*((Fintype.card (TailPerm m):ℝ)⁻¹*
              ∑ τ : TailPerm m,(1/2:ℝ)^nativeMatchingCount
                (G.comap (baseTail σ)) (rankIsolatedSlots ρ K) τ))*
                Fintype.card (TailPerm m) := by
            field_simp [hCP.ne']; ring
          _ ≤ bound*Fintype.card (TailPerm m) :=
            mul_le_mul_of_nonneg_right hmatch hCP.le
  have hr : (K:ℝ)^2*((neuronEvent net hn K T k).card:ℝ) ≤
      400*(Fintype.card (Configuration m):ℝ) := by
    have hh : ((neuronEvent net hn K T k).card:ℝ) ≤
        (400*(Fintype.card (Configuration m):ℝ))/(K:ℝ)^2 := by
      calc
        _ ≤ _ := hmain
        _ = _ := by dsimp only [bound]; ring
    have hc := (le_div_iff (pow_pos hKpos 2)).mp hh
    simpa only [mul_comm] using hc
  exact_mod_cast hr

end MaxCaterpillar.Frontier.RandomRestriction.PerNeuron
