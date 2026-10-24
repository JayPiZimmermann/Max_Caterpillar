import MaxCaterpillar
set_option pp.funBinderTypes true
open BigOperators
open MaxNN MaxCaterpillar
#check @MaxCaterpillar.caterpillar_net
#check @MaxCaterpillar.caterpillar_expansion_choose_le
#check @MaxCaterpillar.caterpillar_expansion_exponential
#check @MaxCaterpillar.caterpillar_expansion_quadratic
#check @MaxCaterpillar.caterpillarDim_ge
#check @MaxCaterpillar.caterpillarDim_eq
#check @MaxCaterpillar.maximum_width
#check @MaxCaterpillar.network_correct
#check @MaxCaterpillar.facet_reduction
#check @MaxCaterpillar.facet_completeness
#check @MaxCaterpillar.coordinate_deletion
#check @MaxCaterpillar.class_identity
#check @MaxCaterpillar.maximum_mem_dictionary
#check @MaxCaterpillar.canonical_expansion
#check @MaxCaterpillar.normalized_cone_count
#check @MaxCaterpillar.width_of_cone_count
#check @MaxCaterpillar.construction_width
#check @MaxCaterpillar.firstWidth_le_square
#check @MaxCaterpillar.firstWidth_le_four_mul_square
#check @MaxCaterpillar.firstWidth_isBigO_square
#check @MaxCaterpillar.coneCount_le_pow
#check @MaxCaterpillar.secondWidth_le_two_mul_pow
#check @MaxCaterpillar.secondWidth_isBigO_pow
#check @MaxCaterpillar.log_secondWidth_le
#check @MaxCaterpillar.log_secondWidth_le_six_mul
#check @MaxCaterpillar.log_secondWidth_isBigO_mul_log
#check @MaxCaterpillar.width_asymptotics
#check @MaxCaterpillar.Internal.ofLayers_eval
#check @MaxCaterpillar.Internal.toReLUNet_eval
#check @MaxCaterpillar.Internal.twoLayerWidth_iff
#check @MaxCaterpillar.Internal.maximum_eq_MAX
#check @MaxCaterpillar.Internal.coneCount_eq_spineConeBound
#check @MaxCaterpillar.network_eval_internal
#check @MaxCaterpillar.maximum_width_rational
#check @MaxCaterpillar.coefficient_rational
#check @MaxCaterpillar.network_rational
#check @MaxCaterpillar.rational_coefficients
#check @MaxCaterpillar.compilation
#check @MaxCaterpillar.quotientDim_eq
#check @MaxCaterpillar.quotient_compression
#check @MaxCaterpillar.maximum_width_one_basis
#check @MaxCaterpillar.quotientDim_add_two_le_secondWidth
#check @MaxCaterpillar.caterpillar_sum_affine
#check @MaxCaterpillar.caterpillar_shared_pieces
#check @MaxCaterpillar.caterpillar_shared_pieces_min
#check @MaxCaterpillar.card_imageSets_le_sum_choose
#check @MaxCaterpillar.wang_sun
#check @MaxCaterpillar.cpwl_two_hidden_layers
#check @MaxCaterpillar.cpwl_two_hidden_layers_shared
#check @MaxCaterpillar.kmps_of_continuous_selection
#check @MaxCaterpillar.kmps_pieces
#check @MaxCaterpillar.cpwl_two_hidden_layers_pieces
#check @MaxCaterpillar.exists_rat_caterpillarExpansion
#check @MaxCaterpillar.caterpillar_sum_affine_rational_pieces
#check @MaxCaterpillar.caterpillar_shared_pieces_rational_pieces
#check @MaxCaterpillar.cpwl_two_hidden_layers_shared_rational
#check @MaxCaterpillar.cpwl_two_hidden_layers_pieces_rational
#check @MaxCaterpillar.max_three_network
#check @MaxCaterpillar.max_four_network
#check @MaxCaterpillar.max_four_identity
#check @MaxCaterpillar.caterpillar_choose_three_le
#check @MaxCaterpillar.caterpillar_count_lower
#check @MaxCaterpillar.caterpillar_count_exponential
#check @MaxCaterpillar.caterpillar_count_exponential_pow
#check @MaxCaterpillar.factorial_le_quotientDim
#check @MaxCaterpillar.SmallN.Max5General4.max_network
#check @MaxCaterpillar.SmallN.Max5Lns27.max_network
#check @MaxCaterpillar.SmallN.Max4Test.max_network
#check @MaxCaterpillar.Frontier.max4_widths_iff
#check @MaxCaterpillar.Frontier.max3_widths_iff
#check @MaxCaterpillar.Frontier.second_width_ge_three
#check @MaxCaterpillar.Frontier.first_width_quadratic
#check @MaxCaterpillar.Frontier.second_width_half
#check @MaxCaterpillar.Frontier.second_width_half_succ
#check @MaxCaterpillar.Frontier.second_width_joint
#check @MaxCaterpillar.Frontier.free_neurons
#check @MaxCaterpillar.Trees.rootedStar_expansion_choose_le
#check @MaxCaterpillar.Trees.rootedStar_expansion_exponential
#check @MaxCaterpillar.Trees.tree_expansion_quadratic
#check @MaxCaterpillar.Trees.tree_bounded_choose_le
#check @MaxCaterpillar.Trees.tree_bounded_exponential
#check @MaxCaterpillar.Trees.tree_star_or_bounded_exponential
#check @MaxCaterpillar.Trees.mixed_expansion_exponential
#check @MaxCaterpillar.caterpillar_net_v4
#check @MaxCaterpillar.bhrsy_parallelepiped_eq_zonotope
#check @MaxCaterpillar.bhrsy_parallelepiped_eq_zonotope_of_nonempty
#check @MaxCaterpillar.bhrsy_parallelepiped_empty
#check @MaxCaterpillar.bhrsy_support_eq
#check @MaxCaterpillar.bhrsy_support_eq_word
#check @MaxCaterpillar.bhrsy_support_mem_caterpillar
#check @MaxCaterpillar.bhrsy_word_mem
#check @MaxCaterpillar.bhrsy_support_empty
#check @MaxCaterpillar.rootedStar_ne_caterpillarFunction
#check @MaxCaterpillar.bhrsy_support_empty_not_caterpillar
#check @MaxCaterpillar.bhrsy_family
#check @MaxCaterpillar.Simplify.tree_outLeaf_choose_le
#check @MaxCaterpillar.Simplify.tree_outLeaf_exponential
#check @MaxCaterpillar.Simplify.mixed_outLeaf_choose_le
#check @MaxCaterpillar.Simplify.mixed_outLeaf_exponential
#check @MaxCaterpillar.Simplify.outLeafBound_of_hubOK
#check @MaxCaterpillar.Simplify.outLeafBound_of_hingeDeg_le
#check @MaxCaterpillar.Simplify.starFace_outLeafBound
#check @MaxCaterpillar.Simplify.factorial_le_quotientDim
#check @MaxCaterpillar.Simplify.brunck_expansion_choose_le
#check @MaxCaterpillar.Simplify.brunck_expansion_exponential
#check @MaxCaterpillar.Simplify.tree_reduced_choose_le
#check @MaxCaterpillar.Simplify.tree_reduced_exponential
#check @MaxCaterpillar.Simplify.tree_reduced_exponential_two
#check @MaxCaterpillar.Audit.exists_isCaterpillarExpansion
#check @MaxCaterpillar.Audit.caterpillarFunction_eq_treeFace
#check @MaxCaterpillar.Simplify.caterpillarFunction_eq_upTree
#check @MaxCaterpillar.Simplify.choose_le_of_red
#check @MaxCaterpillar.Audit.exists_isCaterpillarExpansion
#check @MaxCaterpillar.Audit.caterpillarFunction_eq_treeFace
#check @MaxCaterpillar.Audit.caterpillarFunction_eq_tree
#check @MaxCaterpillar.Audit.exists_isTreeExpansion
#check @MaxCaterpillar.Audit.isTreeExpansion_of_isCaterpillarExpansion
#check @MaxCaterpillar.Audit.exists_isRootedStarExpansion
#check @MaxCaterpillar.Audit.exists_isMixedExpansion
#check @MaxCaterpillar.Audit.second_width_half_succ_satisfiable_three
#check @MaxCaterpillar.Audit.second_width_half_succ_satisfiable_four
#check @MaxCaterpillar.Audit.second_width_joint_hyp_false_three
#check @MaxCaterpillar.Audit.second_width_joint_hyp_false_four
#check @MaxCaterpillar.Audit.free_neurons_satisfiable
#check @MaxCaterpillar.Trees.TreeFace.IsCaterpillar
#print axioms MaxCaterpillar.Audit.exists_isCaterpillarExpansion
#print axioms MaxCaterpillar.Audit.caterpillarFunction_eq_treeFace
#print axioms MaxCaterpillar.Audit.caterpillarFunction_eq_tree
#print axioms MaxCaterpillar.Audit.exists_isTreeExpansion
#print axioms MaxCaterpillar.Audit.isTreeExpansion_of_isCaterpillarExpansion
#print axioms MaxCaterpillar.Audit.exists_isRootedStarExpansion
#print axioms MaxCaterpillar.Audit.exists_isMixedExpansion
#print axioms MaxCaterpillar.Audit.second_width_half_succ_satisfiable_three
#print axioms MaxCaterpillar.Audit.second_width_half_succ_satisfiable_four
#print axioms MaxCaterpillar.Audit.second_width_joint_hyp_false_three
#print axioms MaxCaterpillar.Audit.second_width_joint_hyp_false_four
#print axioms MaxCaterpillar.Audit.free_neurons_satisfiable
