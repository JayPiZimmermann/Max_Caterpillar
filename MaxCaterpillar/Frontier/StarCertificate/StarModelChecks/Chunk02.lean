import MaxCaterpillar.Frontier.StarCertificate.StarCoefficients
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
theorem starVCoefficient_coupling_60 : ∀ (r i : Fin 4),
    starVCoefficient 60 r i = (maskedChain 15 60 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 60) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_60 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 60 r i = (maskedChain 15 60 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 60) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_61 : ∀ (r i : Fin 4),
    starVCoefficient 61 r i = (maskedChain 15 61 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 61) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_61 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 61 r i = (maskedChain 15 61 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 61) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_62 : ∀ (r i : Fin 4),
    starVCoefficient 62 r i = (maskedChain 15 62 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 62) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_62 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 62 r i = (maskedChain 15 62 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 62) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_63 : ∀ (r i : Fin 4),
    starVCoefficient 63 r i = (maskedChain 15 63 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 63) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_63 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 63 r i = (maskedChain 15 63 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 63) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_64 : ∀ (r i : Fin 4),
    starVCoefficient 64 r i = (maskedChain 15 64 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 64) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_64 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 64 r i = (maskedChain 15 64 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 64) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_65 : ∀ (r i : Fin 4),
    starVCoefficient 65 r i = (maskedChain 15 65 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 65) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_65 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 65 r i = (maskedChain 15 65 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 65) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_66 : ∀ (r i : Fin 4),
    starVCoefficient 66 r i = (maskedChain 15 66 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 66) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_66 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 66 r i = (maskedChain 15 66 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 66) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_67 : ∀ (r i : Fin 4),
    starVCoefficient 67 r i = (maskedChain 15 67 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 67) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_67 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 67 r i = (maskedChain 15 67 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 67) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_68 : ∀ (r i : Fin 4),
    starVCoefficient 68 r i = (maskedChain 15 68 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 68) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_68 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 68 r i = (maskedChain 15 68 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 68) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_69 : ∀ (r i : Fin 4),
    starVCoefficient 69 r i = (maskedChain 15 69 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 69) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_69 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 69 r i = (maskedChain 15 69 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 69) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_70 : ∀ (r i : Fin 4),
    starVCoefficient 70 r i = (maskedChain 15 70 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 70) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_70 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 70 r i = (maskedChain 15 70 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 70) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_71 : ∀ (r i : Fin 4),
    starVCoefficient 71 r i = (maskedChain 15 71 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 71) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_71 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 71 r i = (maskedChain 15 71 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 71) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_72 : ∀ (r i : Fin 4),
    starVCoefficient 72 r i = (maskedChain 15 72 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 72) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_72 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 72 r i = (maskedChain 15 72 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 72) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_73 : ∀ (r i : Fin 4),
    starVCoefficient 73 r i = (maskedChain 15 73 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 73) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_73 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 73 r i = (maskedChain 15 73 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 73) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_74 : ∀ (r i : Fin 4),
    starVCoefficient 74 r i = (maskedChain 15 74 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 74) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_74 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 74 r i = (maskedChain 15 74 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 74) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_75 : ∀ (r i : Fin 4),
    starVCoefficient 75 r i = (maskedChain 15 75 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 75) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_75 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 75 r i = (maskedChain 15 75 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 75) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_76 : ∀ (r i : Fin 4),
    starVCoefficient 76 r i = (maskedChain 15 76 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 76) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_76 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 76 r i = (maskedChain 15 76 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 76) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_77 : ∀ (r i : Fin 4),
    starVCoefficient 77 r i = (maskedChain 15 77 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 77) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_77 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 77 r i = (maskedChain 15 77 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 77) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_78 : ∀ (r i : Fin 4),
    starVCoefficient 78 r i = (maskedChain 15 78 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 78) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_78 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 78 r i = (maskedChain 15 78 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 78) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_79 : ∀ (r i : Fin 4),
    starVCoefficient 79 r i = (maskedChain 15 79 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 79) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_79 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 79 r i = (maskedChain 15 79 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 79) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_80 : ∀ (r i : Fin 4),
    starVCoefficient 80 r i = (maskedChain 15 80 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 80) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_80 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 80 r i = (maskedChain 15 80 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 80) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_81 : ∀ (r i : Fin 4),
    starVCoefficient 81 r i = (maskedChain 15 81 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 81) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_81 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 81 r i = (maskedChain 15 81 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 81) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_82 : ∀ (r i : Fin 4),
    starVCoefficient 82 r i = (maskedChain 15 82 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 82) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_82 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 82 r i = (maskedChain 15 82 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 82) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_83 : ∀ (r i : Fin 4),
    starVCoefficient 83 r i = (maskedChain 15 83 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 83) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_83 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 83 r i = (maskedChain 15 83 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 83) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_84 : ∀ (r i : Fin 4),
    starVCoefficient 84 r i = (maskedChain 15 84 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 84) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_84 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 84 r i = (maskedChain 15 84 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 84) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_85 : ∀ (r i : Fin 4),
    starVCoefficient 85 r i = (maskedChain 15 85 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 85) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_85 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 85 r i = (maskedChain 15 85 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 85) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_86 : ∀ (r i : Fin 4),
    starVCoefficient 86 r i = (maskedChain 15 86 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 86) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_86 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 86 r i = (maskedChain 15 86 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 86) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_87 : ∀ (r i : Fin 4),
    starVCoefficient 87 r i = (maskedChain 15 87 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 87) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_87 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 87 r i = (maskedChain 15 87 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 87) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_88 : ∀ (r i : Fin 4),
    starVCoefficient 88 r i = (maskedChain 15 88 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 88) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_88 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 88 r i = (maskedChain 15 88 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 88) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_89 : ∀ (r i : Fin 4),
    starVCoefficient 89 r i = (maskedChain 15 89 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 89) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_89 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 89 r i = (maskedChain 15 89 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 89) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

end MaxCaterpillar.Frontier.StarCertificate
