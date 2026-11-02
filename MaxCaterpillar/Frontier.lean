import MaxCaterpillar.Frontier.Basic
import MaxCaterpillar.Frontier.Asymptotics
import MaxCaterpillar.Frontier.SecondWidth
import MaxCaterpillar.Frontier.FirstWidth
import MaxCaterpillar.Frontier.Constructions
import MaxCaterpillar.Frontier.Main
import MaxCaterpillar.Frontier.GeneralN
import MaxCaterpillar.Frontier.GeneralN2
import MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound

/-! # Width frontiers for two-hidden-layer MAX networks

Headline results in `MaxCaterpillar.Frontier.Main`: `max3_widths_iff`, `max4_widths_iff`,
`second_width_ge_three`, `first_width_ge_four_max3`, `first_width_ge_six_max4`,
`no_one_hidden_max3`. Paper proofs: `research/sN/frontier4/PROOFS.md`.

For arbitrary arity at least 1040, `RandomRestriction.NetworkLowerBound`
proves `h₂ ≥ min(N², N⁴/h₁) / 400000000` for ordinary real networks with
arbitrary biases. Its finite coefficient certificate is a proved dependency.
-/
