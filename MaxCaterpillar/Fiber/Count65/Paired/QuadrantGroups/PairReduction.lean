import MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups.Erasure

/-! # Replace an entire cancelling-jump ray group by two existing slots

One straight physical output interpolation concentrates a ray group. This
avoids iterating cluster transfers. Incoming parameters remain fixed, as do all
spectator outputs. The two resulting weighted preactivations coincide, so a
positive normalization makes their preactivations opposite with outputs ±1.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups

open BigOperators Absorption

noncomputable def sparsePairOutput {k : ℕ} (d : Fin k → ℝ)
    (g : Finset (Fin k)) (p n : Fin k) (C ap an : ℝ) : Fin k → ℝ :=
  fun i => eraseClusterOutput d g i+(if i=p then C/ap else 0)+(if i=n then C/an else 0)

theorem sparsePairOutput_pos {k : ℕ} (d : Fin k → ℝ)
    (g : Finset (Fin k)) (p n : Fin k) (C ap an : ℝ) (hp : p ∈ g) (hpn : p ≠ n) :
    sparsePairOutput d g p n C ap an p = C/ap := by
  simp [sparsePairOutput,eraseClusterOutput,hp,hpn]

theorem sparsePairOutput_neg {k : ℕ} (d : Fin k → ℝ)
    (g : Finset (Fin k)) (p n : Fin k) (C ap an : ℝ) (hn : n ∈ g) (hpn : p ≠ n) :
    sparsePairOutput d g p n C ap an n = C/an := by
  simp [sparsePairOutput,eraseClusterOutput,hn,Ne.symm hpn]

theorem sparsePairOutput_removed {k : ℕ} (d : Fin k → ℝ)
    (g : Finset (Fin k)) (p n i : Fin k) (C ap an : ℝ)
    (hi : i ∈ g) (hip : i ≠ p) (hin : i ≠ n) :
    sparsePairOutput d g p n C ap an i = 0 := by
  simp [sparsePairOutput,eraseClusterOutput,hi,hip,hin]

theorem sparsePairOutput_spectator {k : ℕ} (d : Fin k → ℝ)
    (g : Finset (Fin k)) (p n i : Fin k) (C ap an : ℝ)
    (hp : p ∈ g) (hn : n ∈ g) (hi : i ∉ g) :
    sparsePairOutput d g p n C ap an i = d i := by
  have hip : i ≠ p := by rintro rfl; exact hi hp
  have hin : i ≠ n := by rintro rfl; exact hi hn
  simp [sparsePairOutput,eraseClusterOutput,hi,hip,hin]

private theorem erase_sum_eq_sub {k : ℕ} (d f : Fin k → ℝ) (g : Finset (Fin k)) :
    (∑ i, eraseClusterOutput d g i*f i) = (∑ i, d i*f i)-(∑ i in g, d i*f i) := by
  classical
  have hfilter : Finset.univ.filter (fun i => i ∈ g) = g := by ext i; simp
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (fun i => i ∈ g) (fun i => d i*f i)
  rw [hfilter] at hpartition
  have hout : (∑ i, eraseClusterOutput d g i*f i) =
      ∑ i in Finset.univ.filter (fun i => i ∉ g), d i*f i := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hi : i ∈ g <;> simp [eraseClusterOutput,hi]
  rw [hout]
  linarith only [hpartition]

theorem sparsePairOutput_sum {k : ℕ} (d f : Fin k → ℝ)
    (g : Finset (Fin k)) (p n : Fin k) (C ap an : ℝ)
    (hgroup : (∑ i in g, d i*f i) = (C/ap)*f p+(C/an)*f n) :
    (∑ i, sparsePairOutput d g p n C ap an i*f i) = ∑ i, d i*f i := by
  unfold sparsePairOutput
  simp only [add_mul,Finset.sum_add_distrib,ite_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [erase_sum_eq_sub,hgroup]
  ring

private theorem opposite_weighted_pair (C ap an H : ℝ) (hap : 0 < ap) (han : an < 0) :
    (C/ap)*max 0 (ap*H)+(C/an)*max 0 (an*H) = C*H := by
  have hpos : max 0 (ap*H) = ap*max 0 H := by
    rw [mul_max_of_nonneg _ _ hap.le,mul_zero]
  have hneg : max 0 (an*H) = (-an)*max 0 (-H) := by
    have heq : an*H = (-an)*(-H) := by ring
    rw [heq,mul_max_of_nonneg _ _ (neg_nonneg.mpr han.le),mul_zero]
  have hcp := div_mul_cancel C (ne_of_gt hap)
  have hcn := div_mul_cancel C (ne_of_lt han)
  have hdiff : max 0 H-max 0 (-H) = H := by
    simpa only [max_comm] using max_zero_sub_max_neg_zero_eq_self H
  rw [hpos,hneg]
  calc
    _ = ((C/ap)*ap)*max 0 H-((C/an)*an)*max 0 (-H) := by ring
    _ = C*(max 0 H-max 0 (-H)) := by rw [hcp,hcn]; ring
    _ = C*H := by rw [hdiff]

/-- Functional collinearity and zero total jump determine an exact sparse
physical readout. No sign restriction on the original outputs is needed. -/
theorem sparse_group_pair_eval {N m k : ℕ} (net : Network N m k)
    (g : Finset (Fin k)) (a : Fin k → ℝ) (p n : Fin k)
    (hp : p ∈ g) (hn : n ∈ g) (hap : 0 < a p) (han : a n < 0)
    (hjump : (∑ i in g, net.w₃ i*|a i|) = 0) (H : Point N → ℝ)
    (hpre : ∀ i ∈ g, ∀ x, preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x = a i*H x)
    (x : Point N) :
    (withOutput net (sparsePairOutput net.w₃ g p n
      (∑ i in g, net.w₃ i*max 0 (a i)) (a p) (a n)) net.b₃).eval x = net.eval x := by
  change (∑ i, sparsePairOutput net.w₃ g p n
      (∑ i in g, net.w₃ i*max 0 (a i)) (a p) (a n) i*
        relu (preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x))+net.b₃ =
    (∑ i, net.w₃ i*relu (preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x))+net.b₃
  congr 1
  apply sparsePairOutput_sum
  have hgroup := finite_aligned_group_linear g a (fun _ => 0) net.w₃ 0
    (by intro i _hi; simp) hjump (H x) 0
  simp only [mul_zero,zero_add,add_zero,sub_zero] at hgroup
  have hactual : (∑ i in g, net.w₃ i*relu
      (preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x)) =
      (∑ i in g, net.w₃ i*max 0 (a i))*H x := by
    convert hgroup using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hpre i hi x]
    rfl
  rw [hactual,hpre p hp x,hpre n hn x]
  exact (opposite_weighted_pair _ _ _ _ hap han).symm

theorem sparse_group_pair_joinedIn_exact {N m k : ℕ} [NeZero N]
    (net : Network N m k) (g : Finset (Fin k)) (a : Fin k → ℝ) (p n : Fin k)
    (hp : p ∈ g) (hn : n ∈ g) (hap : 0 < a p) (han : a n < 0)
    (hjump : (∑ i in g, net.w₃ i*|a i|) = 0) (H : Point N → ℝ)
    (hpre : ∀ i ∈ g, ∀ x, preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x = a i*H x)
    (hnet : ∀ x, net.eval x = Maximum N x) :
    JoinedIn (ExactSet N m k) net
      (withOutput net (sparsePairOutput net.w₃ g p n
        (∑ i in g, net.w₃ i*max 0 (a i)) (a p) (a n)) net.b₃) := by
  apply JoinedIn.ofLine (continuous_interpolateOutput net
    (sparsePairOutput net.w₃ g p n (∑ i in g, net.w₃ i*max 0 (a i)) (a p) (a n)) net.b₃).continuousOn
    (interpolateOutput_zero _ _ _) (interpolateOutput_one _ _ _)
  rintro _ ⟨t,_ht,rfl⟩ x
  rw [interpolateOutput_eval,sparse_group_pair_eval net g a p n hp hn hap han hjump H hpre x,
    hnet x]
  ring

theorem sparse_group_pair_sum_preserved {N m k : ℕ} (net : Network N m k)
    (g S : Finset (Fin k)) (hgS : g ⊆ S) (a : Fin k → ℝ) (p n : Fin k)
    (hp : p ∈ g) (hn : n ∈ g) (hap : 0 < a p) (han : a n < 0)
    (hjump : (∑ i in g, net.w₃ i*|a i|) = 0) (H : Point N → ℝ)
    (hpre : ∀ i ∈ g, ∀ x, preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x = a i*H x)
    (x : Point N) :
    (∑ i in S, sparsePairOutput net.w₃ g p n
      (∑ j in g, net.w₃ j*max 0 (a j)) (a p) (a n) i*
        relu (preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x)) =
      ∑ i in S, net.w₃ i*relu (preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x) := by
  classical
  let e := sparsePairOutput net.w₃ g p n (∑ j in g, net.w₃ j*max 0 (a j)) (a p) (a n)
  let f := fun i => relu (preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x)
  have hfull : (∑ i, e i*f i) = ∑ i, net.w₃ i*f i := by
    have h := sparse_group_pair_eval net g a p n hp hn hap han hjump H hpre x
    change (∑ i, e i*f i)+net.b₃ = (∑ i, net.w₃ i*f i)+net.b₃ at h
    exact add_right_cancel h
  have hfilter : Finset.univ.filter (fun i => i ∈ S) = S := by ext i; simp
  have hleft := Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (fun i => i ∈ S) (fun i => e i*f i)
  have hright := Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (fun i => i ∈ S) (fun i => net.w₃ i*f i)
  rw [hfilter] at hleft hright
  have houtside : (∑ i in Finset.univ.filter (fun i => i ∉ S), e i*f i) =
      ∑ i in Finset.univ.filter (fun i => i ∉ S), net.w₃ i*f i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hig : i ∉ g := fun h => (Finset.mem_filter.mp hi).2 (hgS h)
    exact congrArg (fun z : ℝ => z*f i)
      (sparsePairOutput_spectator net.w₃ g p n i _ _ _ hp hn hig)
  change (∑ i in S, e i*f i) = ∑ i in S, net.w₃ i*f i
  linarith only [hfull,hleft,hright,houtside]

theorem sparse_group_pair_weighted_preact {N m k : ℕ} (net : Network N m k)
    (g : Finset (Fin k)) (a : Fin k → ℝ) (p n : Fin k)
    (hp : p ∈ g) (hn : n ∈ g) (hap : 0 < a p) (han : a n < 0) (C : ℝ)
    (H : Point N → ℝ)
    (hpre : ∀ i ∈ g, ∀ x, preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x = a i*H x)
    (x : Point N) :
    sparsePairOutput net.w₃ g p n C (a p) (a n) p*
      preact net.W₁ net.b₁ (net.W₂ p) (net.b₂ p) x =
    sparsePairOutput net.w₃ g p n C (a p) (a n) n*
      preact net.W₁ net.b₁ (net.W₂ n) (net.b₂ n) x := by
  have hpn : p ≠ n := by intro h; rw [h] at hap; linarith only [hap,han]
  rw [sparsePairOutput_pos _ _ _ _ _ _ _ hp hpn,
    sparsePairOutput_neg _ _ _ _ _ _ _ hn hpn,hpre p hp x,hpre n hn x]
  calc
    _ = ((C/a p)*a p)*H x := by ring
    _ = ((C/a n)*a n)*H x := by rw [div_mul_cancel _ (ne_of_gt hap),div_mul_cancel _ (ne_of_lt han)]
    _ = _ := by ring

end MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups
