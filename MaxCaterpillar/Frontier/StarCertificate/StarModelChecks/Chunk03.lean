import MaxCaterpillar.Frontier.StarCertificate.StarCoefficients
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
theorem starVCoefficient_coupling_90 : ∀ (r i : Fin 4),
    starVCoefficient 90 r i = (maskedChain 15 90 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 90) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_90 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 90 r i = (maskedChain 15 90 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 90) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_91 : ∀ (r i : Fin 4),
    starVCoefficient 91 r i = (maskedChain 15 91 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 91) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_91 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 91 r i = (maskedChain 15 91 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 91) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_92 : ∀ (r i : Fin 4),
    starVCoefficient 92 r i = (maskedChain 15 92 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 92) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_92 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 92 r i = (maskedChain 15 92 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 92) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_93 : ∀ (r i : Fin 4),
    starVCoefficient 93 r i = (maskedChain 15 93 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 93) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_93 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 93 r i = (maskedChain 15 93 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 93) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_94 : ∀ (r i : Fin 4),
    starVCoefficient 94 r i = (maskedChain 15 94 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 94) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_94 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 94 r i = (maskedChain 15 94 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 94) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_95 : ∀ (r i : Fin 4),
    starVCoefficient 95 r i = (maskedChain 15 95 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 95) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_95 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 95 r i = (maskedChain 15 95 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 95) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_96 : ∀ (r i : Fin 4),
    starVCoefficient 96 r i = (maskedChain 15 96 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 96) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_96 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 96 r i = (maskedChain 15 96 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 96) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_97 : ∀ (r i : Fin 4),
    starVCoefficient 97 r i = (maskedChain 15 97 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 97) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_97 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 97 r i = (maskedChain 15 97 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 97) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_98 : ∀ (r i : Fin 4),
    starVCoefficient 98 r i = (maskedChain 15 98 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 98) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_98 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 98 r i = (maskedChain 15 98 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 98) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_99 : ∀ (r i : Fin 4),
    starVCoefficient 99 r i = (maskedChain 15 99 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 99) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_99 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 99 r i = (maskedChain 15 99 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 99) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_100 : ∀ (r i : Fin 4),
    starVCoefficient 100 r i = (maskedChain 15 100 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 100) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_100 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 100 r i = (maskedChain 15 100 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 100) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_101 : ∀ (r i : Fin 4),
    starVCoefficient 101 r i = (maskedChain 15 101 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 101) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_101 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 101 r i = (maskedChain 15 101 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 101) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_102 : ∀ (r i : Fin 4),
    starVCoefficient 102 r i = (maskedChain 15 102 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 102) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_102 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 102 r i = (maskedChain 15 102 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 102) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_103 : ∀ (r i : Fin 4),
    starVCoefficient 103 r i = (maskedChain 15 103 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 103) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_103 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 103 r i = (maskedChain 15 103 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 103) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_104 : ∀ (r i : Fin 4),
    starVCoefficient 104 r i = (maskedChain 15 104 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 104) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_104 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 104 r i = (maskedChain 15 104 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 104) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_105 : ∀ (r i : Fin 4),
    starVCoefficient 105 r i = (maskedChain 15 105 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 105) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_105 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 105 r i = (maskedChain 15 105 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 105) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_106 : ∀ (r i : Fin 4),
    starVCoefficient 106 r i = (maskedChain 15 106 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 106) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_106 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 106 r i = (maskedChain 15 106 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 106) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_107 : ∀ (r i : Fin 4),
    starVCoefficient 107 r i = (maskedChain 15 107 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 107) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_107 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 107 r i = (maskedChain 15 107 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 107) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_108 : ∀ (r i : Fin 4),
    starVCoefficient 108 r i = (maskedChain 15 108 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 108) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_108 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 108 r i = (maskedChain 15 108 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 108) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_109 : ∀ (r i : Fin 4),
    starVCoefficient 109 r i = (maskedChain 15 109 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 109) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_109 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 109 r i = (maskedChain 15 109 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 109) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_110 : ∀ (r i : Fin 4),
    starVCoefficient 110 r i = (maskedChain 15 110 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 110) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_110 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 110 r i = (maskedChain 15 110 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 110) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_111 : ∀ (r i : Fin 4),
    starVCoefficient 111 r i = (maskedChain 15 111 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 111) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_111 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 111 r i = (maskedChain 15 111 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 111) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_112 : ∀ (r i : Fin 4),
    starVCoefficient 112 r i = (maskedChain 15 112 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 112) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_112 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 112 r i = (maskedChain 15 112 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 112) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_113 : ∀ (r i : Fin 4),
    starVCoefficient 113 r i = (maskedChain 15 113 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 113) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_113 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 113 r i = (maskedChain 15 113 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 113) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_114 : ∀ (r i : Fin 4),
    starVCoefficient 114 r i = (maskedChain 15 114 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 114) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_114 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 114 r i = (maskedChain 15 114 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 114) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_115 : ∀ (r i : Fin 4),
    starVCoefficient 115 r i = (maskedChain 15 115 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 115) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_115 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 115 r i = (maskedChain 15 115 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 115) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_116 : ∀ (r i : Fin 4),
    starVCoefficient 116 r i = (maskedChain 15 116 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 116) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_116 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 116 r i = (maskedChain 15 116 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 116) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_117 : ∀ (r i : Fin 4),
    starVCoefficient 117 r i = (maskedChain 15 117 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 117) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_117 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 117 r i = (maskedChain 15 117 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 117) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_118 : ∀ (r i : Fin 4),
    starVCoefficient 118 r i = (maskedChain 15 118 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 118) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_118 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 118 r i = (maskedChain 15 118 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 118) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVCoefficient_coupling_119 : ∀ (r i : Fin 4),
    starVCoefficient 119 r i = (maskedChain 15 119 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 119) then 1 else 0) :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem starVPrimeCoefficient_coupling_119 : ∀ (r i : Fin 4),
    starVPrimeCoefficient 119 r i = (maskedChain 15 119 r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask 119) then 0 else 1) :=
  of_decide_eq_true (by with_unfolding_all rfl)

end MaxCaterpillar.Frontier.StarCertificate
