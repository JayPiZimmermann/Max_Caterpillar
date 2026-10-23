# Frontier formalization progress (agent notes; restart from here)

Plan (simplified proof route, all proofs in zero-bias model `ZNet`):
- Basic.lean: `lin`, `diag`, Maximum helpers, `ZNet`, zero-bias reduction (Hertrich 2.3 via
  scaling + continuity in the bias scale), `OddLin` / `LocAff` / `LocOddLin`,
  `not_locOddLin_max` (odd part max+min is not linear where >= 3 coords tie at top).
  Lemma 0' becomes: max_N not OddLin (f(x)-f(-x) linear) for N>=3.
- Asymptotics.lean: eventual behaviour along x + t1 (E1 slope, E2 identity), via `negIn` for -inf.
  Lemma S: rows with s_j >= 0 have trivial common kernel (compare F(w+t1)=F(t1)), so N <= #{s>=0}.
- SecondWidth.lean: Theorem 1 (h2 <= 2 impossible, N >= 3).
- FirstWidth.lean: N=3 h1>=4 (S + J- nonempty); N=4: h1=5 forces |J+|=1,|J0|=3; Lemma M via
  dual vectors u_j and matrix D_ij = u_j(i) - l(u_j) gives i0 with A_j(i0) != 0 for all J0 rows;
  germ (LocOddLin) at -e_{i0} contradicts.
- Constructions.lean, Main.lean: nets (4,6,3), (3,4,3), padding, iff theorems.

Status:
- [done] Basic.lean compiles (zero-bias reduction `Network.eval_zeroBias_of_posHom`,
  `Network.toZ_eval_of_max`, `not_locOddLin_max`, `not_oddLin_max`).
- [done] Asymptotics.lean compiles (`ZNet.max_plus`, `ZNet.max_minus`, `ZNet.ker_plus/minus`,
  `ZNet.card_nonneg/nonpos`, `ZNet.exists_pos/neg`).
- [done] SecondWidth.lean compiles: `ZNet.second_width_ge_three` (Theorem 1, any N >= 3).
- [done] FirstWidth.lean compiles: `ZNet.first_width_ge_succ`, `lemmaM_core`, `ZNet.lemmaM`, `ZNet.first_width_ge_four_max3`, `ZNet.first_width_ge_six_max4`.
- [done] Constructions.lean compiles: `maxThreeNet_eval`, `maxFourNet_eval`, `Network.padFirst_eval`, `exists_network_of_le`.
- [done] Main.lean + Frontier.lean aggregator: `max4_widths_iff`, `max3_widths_iff` etc.; lake build MaxCaterpillar.Frontier green; axioms propext/Classical.choice/Quot.sound.
