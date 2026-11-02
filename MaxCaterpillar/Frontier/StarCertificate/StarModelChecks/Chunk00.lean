import MaxCaterpillar.Frontier.StarCertificate.StarCoefficients
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
theorem starVCoefficient_coupling_0 : ∀ (r i : Fin 4),
    starVCoefficient 0 r i = (maskedChain 15 0 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 0) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_0 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 0 r i = (maskedChain 15 0 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 0) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_1 : ∀ (r i : Fin 4),
    starVCoefficient 1 r i = (maskedChain 15 1 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 1) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_1 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 1 r i = (maskedChain 15 1 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 1) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_2 : ∀ (r i : Fin 4),
    starVCoefficient 2 r i = (maskedChain 15 2 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 2) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_2 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 2 r i = (maskedChain 15 2 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 2) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_3 : ∀ (r i : Fin 4),
    starVCoefficient 3 r i = (maskedChain 15 3 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 3) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_3 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 3 r i = (maskedChain 15 3 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 3) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_4 : ∀ (r i : Fin 4),
    starVCoefficient 4 r i = (maskedChain 15 4 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 4) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_4 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 4 r i = (maskedChain 15 4 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 4) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_5 : ∀ (r i : Fin 4),
    starVCoefficient 5 r i = (maskedChain 15 5 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 5) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_5 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 5 r i = (maskedChain 15 5 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 5) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_6 : ∀ (r i : Fin 4),
    starVCoefficient 6 r i = (maskedChain 15 6 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 6) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_6 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 6 r i = (maskedChain 15 6 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 6) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_7 : ∀ (r i : Fin 4),
    starVCoefficient 7 r i = (maskedChain 15 7 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 7) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_7 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 7 r i = (maskedChain 15 7 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 7) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_8 : ∀ (r i : Fin 4),
    starVCoefficient 8 r i = (maskedChain 15 8 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 8) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_8 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 8 r i = (maskedChain 15 8 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 8) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_9 : ∀ (r i : Fin 4),
    starVCoefficient 9 r i = (maskedChain 15 9 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 9) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_9 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 9 r i = (maskedChain 15 9 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 9) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_10 : ∀ (r i : Fin 4),
    starVCoefficient 10 r i = (maskedChain 15 10 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 10) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_10 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 10 r i = (maskedChain 15 10 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 10) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_11 : ∀ (r i : Fin 4),
    starVCoefficient 11 r i = (maskedChain 15 11 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 11) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_11 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 11 r i = (maskedChain 15 11 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 11) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_12 : ∀ (r i : Fin 4),
    starVCoefficient 12 r i = (maskedChain 15 12 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 12) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_12 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 12 r i = (maskedChain 15 12 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 12) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_13 : ∀ (r i : Fin 4),
    starVCoefficient 13 r i = (maskedChain 15 13 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 13) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_13 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 13 r i = (maskedChain 15 13 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 13) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_14 : ∀ (r i : Fin 4),
    starVCoefficient 14 r i = (maskedChain 15 14 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 14) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_14 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 14 r i = (maskedChain 15 14 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 14) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_15 : ∀ (r i : Fin 4),
    starVCoefficient 15 r i = (maskedChain 15 15 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 15) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_15 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 15 r i = (maskedChain 15 15 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 15) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_16 : ∀ (r i : Fin 4),
    starVCoefficient 16 r i = (maskedChain 15 16 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 16) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_16 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 16 r i = (maskedChain 15 16 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 16) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_17 : ∀ (r i : Fin 4),
    starVCoefficient 17 r i = (maskedChain 15 17 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 17) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_17 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 17 r i = (maskedChain 15 17 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 17) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_18 : ∀ (r i : Fin 4),
    starVCoefficient 18 r i = (maskedChain 15 18 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 18) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_18 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 18 r i = (maskedChain 15 18 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 18) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_19 : ∀ (r i : Fin 4),
    starVCoefficient 19 r i = (maskedChain 15 19 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 19) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_19 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 19 r i = (maskedChain 15 19 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 19) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_20 : ∀ (r i : Fin 4),
    starVCoefficient 20 r i = (maskedChain 15 20 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 20) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_20 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 20 r i = (maskedChain 15 20 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 20) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_21 : ∀ (r i : Fin 4),
    starVCoefficient 21 r i = (maskedChain 15 21 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 21) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_21 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 21 r i = (maskedChain 15 21 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 21) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_22 : ∀ (r i : Fin 4),
    starVCoefficient 22 r i = (maskedChain 15 22 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 22) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_22 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 22 r i = (maskedChain 15 22 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 22) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_23 : ∀ (r i : Fin 4),
    starVCoefficient 23 r i = (maskedChain 15 23 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 23) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_23 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 23 r i = (maskedChain 15 23 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 23) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_24 : ∀ (r i : Fin 4),
    starVCoefficient 24 r i = (maskedChain 15 24 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 24) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_24 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 24 r i = (maskedChain 15 24 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 24) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_25 : ∀ (r i : Fin 4),
    starVCoefficient 25 r i = (maskedChain 15 25 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 25) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_25 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 25 r i = (maskedChain 15 25 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 25) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_26 : ∀ (r i : Fin 4),
    starVCoefficient 26 r i = (maskedChain 15 26 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 26) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_26 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 26 r i = (maskedChain 15 26 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 26) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_27 : ∀ (r i : Fin 4),
    starVCoefficient 27 r i = (maskedChain 15 27 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 27) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_27 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 27 r i = (maskedChain 15 27 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 27) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_28 : ∀ (r i : Fin 4),
    starVCoefficient 28 r i = (maskedChain 15 28 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 28) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_28 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 28 r i = (maskedChain 15 28 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 28) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_29 : ∀ (r i : Fin 4),
    starVCoefficient 29 r i = (maskedChain 15 29 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 29) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_29 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 29 r i = (maskedChain 15 29 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 29) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

end MaxCaterpillar.Frontier.StarCertificate
