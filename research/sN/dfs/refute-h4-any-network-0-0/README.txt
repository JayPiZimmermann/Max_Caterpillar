Adversarial check of h4-any-network generic-locality lemma (m=3 characterization).
Verdict: not refuted. Hand re-derivation of x_o / s coefficients, germ v_t = Gamma_t - d_t,
translation invariance from (c), and the 8-corner collapse all agree with the claim, for signed c_e.
check_m3.py: independent exact (Fraction) evaluation of actual neurons
  g = l.x + sum C_ij relu(x_i-x_j) + sum a_i relu(x_i)+b_i relu(-x_i) + bias  (signed integer weights, N=3..6)
at a random point of the cell, third mixed difference with delta=1e-6, vs closed form (a),(c),(Lambda), bias=0.
70% of trials forced to vanish on the cell. Result (check_m3.log): 20000 trials, 0 mismatches, 8237 nonzero.
Scope remark: with a second-layer bias, g==0 on the (conic) cell forces bias=0, so the claim's bias-free normal form is no loss.
