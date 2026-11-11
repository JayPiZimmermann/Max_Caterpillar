import MaxCaterpillar.Frontier.StarCertificate.XiSelectorChecks.Chunk00
import MaxCaterpillar.Frontier.StarCertificate.XiSelectorChecks.Chunk01
import MaxCaterpillar.Frontier.StarCertificate.XiSelectorChecks.Chunk02
import MaxCaterpillar.Frontier.StarCertificate.XiSelectorChecks.Chunk03
import MaxCaterpillar.Frontier.StarCertificate.XiSelectorChecks.Chunk04
import MaxCaterpillar.Frontier.StarCertificate.XiSelectorChecks.Chunk05
import MaxCaterpillar.Frontier.StarCertificate.XiSelectorChecks.Chunk06
import MaxCaterpillar.Frontier.StarCertificate.XiSelectorChecks.Chunk07
import MaxCaterpillar.Frontier.StarCertificate.XiSelectorChecks.Chunk08
import MaxCaterpillar.Frontier.StarCertificate.XiSelectorChecks.Chunk09
import MaxCaterpillar.Frontier.StarCertificate.XiSelectorChecks.Chunk10
import MaxCaterpillar.Frontier.StarCertificate.XiSelectorChecks.Chunk11
import MaxCaterpillar.Frontier.StarCertificate.XiSelectorChecks.Chunk12
import MaxCaterpillar.Frontier.StarCertificate.XiSelectorChecks.Chunk13
import MaxCaterpillar.Frontier.StarCertificate.XiSelectorChecks.Chunk14

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem masked_compatible (T : Fin 16) (p : Fin 120) (t : Fin 10) (i : Fin 4) :
    (maskedCoarse T p t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T p j).form subsetForms i := by
  fin_cases p
  · exact masked_compatible_0 T t i
  · exact masked_compatible_1 T t i
  · exact masked_compatible_2 T t i
  · exact masked_compatible_3 T t i
  · exact masked_compatible_4 T t i
  · exact masked_compatible_5 T t i
  · exact masked_compatible_6 T t i
  · exact masked_compatible_7 T t i
  · exact masked_compatible_8 T t i
  · exact masked_compatible_9 T t i
  · exact masked_compatible_10 T t i
  · exact masked_compatible_11 T t i
  · exact masked_compatible_12 T t i
  · exact masked_compatible_13 T t i
  · exact masked_compatible_14 T t i
  · exact masked_compatible_15 T t i
  · exact masked_compatible_16 T t i
  · exact masked_compatible_17 T t i
  · exact masked_compatible_18 T t i
  · exact masked_compatible_19 T t i
  · exact masked_compatible_20 T t i
  · exact masked_compatible_21 T t i
  · exact masked_compatible_22 T t i
  · exact masked_compatible_23 T t i
  · exact masked_compatible_24 T t i
  · exact masked_compatible_25 T t i
  · exact masked_compatible_26 T t i
  · exact masked_compatible_27 T t i
  · exact masked_compatible_28 T t i
  · exact masked_compatible_29 T t i
  · exact masked_compatible_30 T t i
  · exact masked_compatible_31 T t i
  · exact masked_compatible_32 T t i
  · exact masked_compatible_33 T t i
  · exact masked_compatible_34 T t i
  · exact masked_compatible_35 T t i
  · exact masked_compatible_36 T t i
  · exact masked_compatible_37 T t i
  · exact masked_compatible_38 T t i
  · exact masked_compatible_39 T t i
  · exact masked_compatible_40 T t i
  · exact masked_compatible_41 T t i
  · exact masked_compatible_42 T t i
  · exact masked_compatible_43 T t i
  · exact masked_compatible_44 T t i
  · exact masked_compatible_45 T t i
  · exact masked_compatible_46 T t i
  · exact masked_compatible_47 T t i
  · exact masked_compatible_48 T t i
  · exact masked_compatible_49 T t i
  · exact masked_compatible_50 T t i
  · exact masked_compatible_51 T t i
  · exact masked_compatible_52 T t i
  · exact masked_compatible_53 T t i
  · exact masked_compatible_54 T t i
  · exact masked_compatible_55 T t i
  · exact masked_compatible_56 T t i
  · exact masked_compatible_57 T t i
  · exact masked_compatible_58 T t i
  · exact masked_compatible_59 T t i
  · exact masked_compatible_60 T t i
  · exact masked_compatible_61 T t i
  · exact masked_compatible_62 T t i
  · exact masked_compatible_63 T t i
  · exact masked_compatible_64 T t i
  · exact masked_compatible_65 T t i
  · exact masked_compatible_66 T t i
  · exact masked_compatible_67 T t i
  · exact masked_compatible_68 T t i
  · exact masked_compatible_69 T t i
  · exact masked_compatible_70 T t i
  · exact masked_compatible_71 T t i
  · exact masked_compatible_72 T t i
  · exact masked_compatible_73 T t i
  · exact masked_compatible_74 T t i
  · exact masked_compatible_75 T t i
  · exact masked_compatible_76 T t i
  · exact masked_compatible_77 T t i
  · exact masked_compatible_78 T t i
  · exact masked_compatible_79 T t i
  · exact masked_compatible_80 T t i
  · exact masked_compatible_81 T t i
  · exact masked_compatible_82 T t i
  · exact masked_compatible_83 T t i
  · exact masked_compatible_84 T t i
  · exact masked_compatible_85 T t i
  · exact masked_compatible_86 T t i
  · exact masked_compatible_87 T t i
  · exact masked_compatible_88 T t i
  · exact masked_compatible_89 T t i
  · exact masked_compatible_90 T t i
  · exact masked_compatible_91 T t i
  · exact masked_compatible_92 T t i
  · exact masked_compatible_93 T t i
  · exact masked_compatible_94 T t i
  · exact masked_compatible_95 T t i
  · exact masked_compatible_96 T t i
  · exact masked_compatible_97 T t i
  · exact masked_compatible_98 T t i
  · exact masked_compatible_99 T t i
  · exact masked_compatible_100 T t i
  · exact masked_compatible_101 T t i
  · exact masked_compatible_102 T t i
  · exact masked_compatible_103 T t i
  · exact masked_compatible_104 T t i
  · exact masked_compatible_105 T t i
  · exact masked_compatible_106 T t i
  · exact masked_compatible_107 T t i
  · exact masked_compatible_108 T t i
  · exact masked_compatible_109 T t i
  · exact masked_compatible_110 T t i
  · exact masked_compatible_111 T t i
  · exact masked_compatible_112 T t i
  · exact masked_compatible_113 T t i
  · exact masked_compatible_114 T t i
  · exact masked_compatible_115 T t i
  · exact masked_compatible_116 T t i
  · exact masked_compatible_117 T t i
  · exact masked_compatible_118 T t i
  · exact masked_compatible_119 T t i

theorem chain_masked_projection (T : Fin 16) (p : Fin 120) (j i : Fin 4) :
    (maskedChain T p j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 p j).form subsetForms i else 0 := by
  fin_cases p
  · exact chain_masked_projection_0 T j i
  · exact chain_masked_projection_1 T j i
  · exact chain_masked_projection_2 T j i
  · exact chain_masked_projection_3 T j i
  · exact chain_masked_projection_4 T j i
  · exact chain_masked_projection_5 T j i
  · exact chain_masked_projection_6 T j i
  · exact chain_masked_projection_7 T j i
  · exact chain_masked_projection_8 T j i
  · exact chain_masked_projection_9 T j i
  · exact chain_masked_projection_10 T j i
  · exact chain_masked_projection_11 T j i
  · exact chain_masked_projection_12 T j i
  · exact chain_masked_projection_13 T j i
  · exact chain_masked_projection_14 T j i
  · exact chain_masked_projection_15 T j i
  · exact chain_masked_projection_16 T j i
  · exact chain_masked_projection_17 T j i
  · exact chain_masked_projection_18 T j i
  · exact chain_masked_projection_19 T j i
  · exact chain_masked_projection_20 T j i
  · exact chain_masked_projection_21 T j i
  · exact chain_masked_projection_22 T j i
  · exact chain_masked_projection_23 T j i
  · exact chain_masked_projection_24 T j i
  · exact chain_masked_projection_25 T j i
  · exact chain_masked_projection_26 T j i
  · exact chain_masked_projection_27 T j i
  · exact chain_masked_projection_28 T j i
  · exact chain_masked_projection_29 T j i
  · exact chain_masked_projection_30 T j i
  · exact chain_masked_projection_31 T j i
  · exact chain_masked_projection_32 T j i
  · exact chain_masked_projection_33 T j i
  · exact chain_masked_projection_34 T j i
  · exact chain_masked_projection_35 T j i
  · exact chain_masked_projection_36 T j i
  · exact chain_masked_projection_37 T j i
  · exact chain_masked_projection_38 T j i
  · exact chain_masked_projection_39 T j i
  · exact chain_masked_projection_40 T j i
  · exact chain_masked_projection_41 T j i
  · exact chain_masked_projection_42 T j i
  · exact chain_masked_projection_43 T j i
  · exact chain_masked_projection_44 T j i
  · exact chain_masked_projection_45 T j i
  · exact chain_masked_projection_46 T j i
  · exact chain_masked_projection_47 T j i
  · exact chain_masked_projection_48 T j i
  · exact chain_masked_projection_49 T j i
  · exact chain_masked_projection_50 T j i
  · exact chain_masked_projection_51 T j i
  · exact chain_masked_projection_52 T j i
  · exact chain_masked_projection_53 T j i
  · exact chain_masked_projection_54 T j i
  · exact chain_masked_projection_55 T j i
  · exact chain_masked_projection_56 T j i
  · exact chain_masked_projection_57 T j i
  · exact chain_masked_projection_58 T j i
  · exact chain_masked_projection_59 T j i
  · exact chain_masked_projection_60 T j i
  · exact chain_masked_projection_61 T j i
  · exact chain_masked_projection_62 T j i
  · exact chain_masked_projection_63 T j i
  · exact chain_masked_projection_64 T j i
  · exact chain_masked_projection_65 T j i
  · exact chain_masked_projection_66 T j i
  · exact chain_masked_projection_67 T j i
  · exact chain_masked_projection_68 T j i
  · exact chain_masked_projection_69 T j i
  · exact chain_masked_projection_70 T j i
  · exact chain_masked_projection_71 T j i
  · exact chain_masked_projection_72 T j i
  · exact chain_masked_projection_73 T j i
  · exact chain_masked_projection_74 T j i
  · exact chain_masked_projection_75 T j i
  · exact chain_masked_projection_76 T j i
  · exact chain_masked_projection_77 T j i
  · exact chain_masked_projection_78 T j i
  · exact chain_masked_projection_79 T j i
  · exact chain_masked_projection_80 T j i
  · exact chain_masked_projection_81 T j i
  · exact chain_masked_projection_82 T j i
  · exact chain_masked_projection_83 T j i
  · exact chain_masked_projection_84 T j i
  · exact chain_masked_projection_85 T j i
  · exact chain_masked_projection_86 T j i
  · exact chain_masked_projection_87 T j i
  · exact chain_masked_projection_88 T j i
  · exact chain_masked_projection_89 T j i
  · exact chain_masked_projection_90 T j i
  · exact chain_masked_projection_91 T j i
  · exact chain_masked_projection_92 T j i
  · exact chain_masked_projection_93 T j i
  · exact chain_masked_projection_94 T j i
  · exact chain_masked_projection_95 T j i
  · exact chain_masked_projection_96 T j i
  · exact chain_masked_projection_97 T j i
  · exact chain_masked_projection_98 T j i
  · exact chain_masked_projection_99 T j i
  · exact chain_masked_projection_100 T j i
  · exact chain_masked_projection_101 T j i
  · exact chain_masked_projection_102 T j i
  · exact chain_masked_projection_103 T j i
  · exact chain_masked_projection_104 T j i
  · exact chain_masked_projection_105 T j i
  · exact chain_masked_projection_106 T j i
  · exact chain_masked_projection_107 T j i
  · exact chain_masked_projection_108 T j i
  · exact chain_masked_projection_109 T j i
  · exact chain_masked_projection_110 T j i
  · exact chain_masked_projection_111 T j i
  · exact chain_masked_projection_112 T j i
  · exact chain_masked_projection_113 T j i
  · exact chain_masked_projection_114 T j i
  · exact chain_masked_projection_115 T j i
  · exact chain_masked_projection_116 T j i
  · exact chain_masked_projection_117 T j i
  · exact chain_masked_projection_118 T j i
  · exact chain_masked_projection_119 T j i

end MaxCaterpillar.Frontier.StarCertificate
