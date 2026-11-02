import MaxCaterpillar.Frontier.StarCertificate.StarCoefficients
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
theorem starVCoefficient_coupling_30 : ∀ (r i : Fin 4),
    starVCoefficient 30 r i = (maskedChain 15 30 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 30) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_30 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 30 r i = (maskedChain 15 30 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 30) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_31 : ∀ (r i : Fin 4),
    starVCoefficient 31 r i = (maskedChain 15 31 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 31) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_31 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 31 r i = (maskedChain 15 31 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 31) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_32 : ∀ (r i : Fin 4),
    starVCoefficient 32 r i = (maskedChain 15 32 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 32) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_32 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 32 r i = (maskedChain 15 32 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 32) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_33 : ∀ (r i : Fin 4),
    starVCoefficient 33 r i = (maskedChain 15 33 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 33) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_33 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 33 r i = (maskedChain 15 33 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 33) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_34 : ∀ (r i : Fin 4),
    starVCoefficient 34 r i = (maskedChain 15 34 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 34) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_34 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 34 r i = (maskedChain 15 34 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 34) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_35 : ∀ (r i : Fin 4),
    starVCoefficient 35 r i = (maskedChain 15 35 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 35) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_35 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 35 r i = (maskedChain 15 35 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 35) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_36 : ∀ (r i : Fin 4),
    starVCoefficient 36 r i = (maskedChain 15 36 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 36) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_36 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 36 r i = (maskedChain 15 36 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 36) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_37 : ∀ (r i : Fin 4),
    starVCoefficient 37 r i = (maskedChain 15 37 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 37) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_37 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 37 r i = (maskedChain 15 37 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 37) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_38 : ∀ (r i : Fin 4),
    starVCoefficient 38 r i = (maskedChain 15 38 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 38) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_38 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 38 r i = (maskedChain 15 38 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 38) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_39 : ∀ (r i : Fin 4),
    starVCoefficient 39 r i = (maskedChain 15 39 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 39) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_39 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 39 r i = (maskedChain 15 39 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 39) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_40 : ∀ (r i : Fin 4),
    starVCoefficient 40 r i = (maskedChain 15 40 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 40) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_40 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 40 r i = (maskedChain 15 40 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 40) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_41 : ∀ (r i : Fin 4),
    starVCoefficient 41 r i = (maskedChain 15 41 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 41) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_41 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 41 r i = (maskedChain 15 41 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 41) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_42 : ∀ (r i : Fin 4),
    starVCoefficient 42 r i = (maskedChain 15 42 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 42) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_42 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 42 r i = (maskedChain 15 42 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 42) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_43 : ∀ (r i : Fin 4),
    starVCoefficient 43 r i = (maskedChain 15 43 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 43) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_43 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 43 r i = (maskedChain 15 43 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 43) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_44 : ∀ (r i : Fin 4),
    starVCoefficient 44 r i = (maskedChain 15 44 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 44) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_44 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 44 r i = (maskedChain 15 44 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 44) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_45 : ∀ (r i : Fin 4),
    starVCoefficient 45 r i = (maskedChain 15 45 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 45) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_45 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 45 r i = (maskedChain 15 45 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 45) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_46 : ∀ (r i : Fin 4),
    starVCoefficient 46 r i = (maskedChain 15 46 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 46) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_46 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 46 r i = (maskedChain 15 46 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 46) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_47 : ∀ (r i : Fin 4),
    starVCoefficient 47 r i = (maskedChain 15 47 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 47) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_47 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 47 r i = (maskedChain 15 47 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 47) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_48 : ∀ (r i : Fin 4),
    starVCoefficient 48 r i = (maskedChain 15 48 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 48) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_48 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 48 r i = (maskedChain 15 48 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 48) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_49 : ∀ (r i : Fin 4),
    starVCoefficient 49 r i = (maskedChain 15 49 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 49) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_49 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 49 r i = (maskedChain 15 49 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 49) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_50 : ∀ (r i : Fin 4),
    starVCoefficient 50 r i = (maskedChain 15 50 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 50) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_50 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 50 r i = (maskedChain 15 50 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 50) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_51 : ∀ (r i : Fin 4),
    starVCoefficient 51 r i = (maskedChain 15 51 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 51) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_51 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 51 r i = (maskedChain 15 51 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 51) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_52 : ∀ (r i : Fin 4),
    starVCoefficient 52 r i = (maskedChain 15 52 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 52) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_52 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 52 r i = (maskedChain 15 52 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 52) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_53 : ∀ (r i : Fin 4),
    starVCoefficient 53 r i = (maskedChain 15 53 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 53) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_53 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 53 r i = (maskedChain 15 53 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 53) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_54 : ∀ (r i : Fin 4),
    starVCoefficient 54 r i = (maskedChain 15 54 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 54) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_54 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 54 r i = (maskedChain 15 54 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 54) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_55 : ∀ (r i : Fin 4),
    starVCoefficient 55 r i = (maskedChain 15 55 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 55) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_55 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 55 r i = (maskedChain 15 55 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 55) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_56 : ∀ (r i : Fin 4),
    starVCoefficient 56 r i = (maskedChain 15 56 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 56) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_56 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 56 r i = (maskedChain 15 56 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 56) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_57 : ∀ (r i : Fin 4),
    starVCoefficient 57 r i = (maskedChain 15 57 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 57) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_57 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 57 r i = (maskedChain 15 57 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 57) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_58 : ∀ (r i : Fin 4),
    starVCoefficient 58 r i = (maskedChain 15 58 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 58) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_58 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 58 r i = (maskedChain 15 58 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 58) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_59 : ∀ (r i : Fin 4),
    starVCoefficient 59 r i = (maskedChain 15 59 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 59) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_59 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 59 r i = (maskedChain 15 59 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 59) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

end MaxCaterpillar.Frontier.StarCertificate
