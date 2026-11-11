import MaxCaterpillar.Fiber.Count65.TwoRoots.OneActive

/-! # The outward adjacent-root branch is impossible at every second width -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.TwoRoots
open MaxCaterpillar.Frontier

noncomputable def outwardRows (a b c : ℝ) (t : Point 4) : Fin 4 → Point 4 :=
  ![![-1,1,0,0], ![0,1,-1,0], ![a,0,b,c], t]

lemma third_nonneg_of_inactive_roots (A : Fin 4 → Point 4) (h : Represents A)
    (q : Point 4) (i k : Fin 4) (hik : i ≠ k)
    (hi : q i = Maximum 4 q) (hk : q k = Maximum 4 q)
    (h0 : lin (A 0) q < 0) (h1 : lin (A 1) q < 0)
    (ht : Nonroot (A 3)) : 0 ≤ lin (A 2) q := by
  apply nonroot_nonneg_of_two_possible A h q i k 2 3 hik hi hk _ ht
  intro j hj2 hj3
  fin_cases j
  · exact h0
  · exact h1
  · exact False.elim (hj2 rfl)
  · exact False.elim (hj3 rfl)

/-- C3's omitted-center row cannot accompany two outward roots.
The second nonroot and the entire decoder have arbitrary real coefficients. -/
theorem outward_fork_excluded (a b c : ℝ) (t : Point 4)
    (hsum : a+b+c = 0) (ha : a ≠ 0) (ht : Nonroot t) :
    ¬ Represents (outwardRows a b c t) := by
  intro h
  have hn (q : Point 4) (i k : Fin 4) (hik : i ≠ k)
      (hi : q i = Maximum 4 q) (hk : q k = Maximum 4 q)
      (h0 : lin (outwardRows a b c t 0) q < 0)
      (h1 : lin (outwardRows a b c t 1) q < 0) :
      0 ≤ lin (outwardRows a b c t 2) q :=
    third_nonneg_of_inactive_roots _ h q i k hik hi hk h0 h1 (by simpa [outwardRows] using ht)
  have hc := hn ![0,-1,0,-1] 0 2 (by decide)
    (by norm_num [Maximum_four]) (by norm_num [Maximum_four])
    (by norm_num [lin_four,outwardRows]) (by norm_num [lin_four,outwardRows])
  have hb := hn ![0,-2,-1,0] 0 3 (by decide)
    (by norm_num [Maximum_four]) (by norm_num [Maximum_four])
    (by norm_num [lin_four,outwardRows]) (by norm_num [lin_four,outwardRows])
  have haa := hn ![-1,-2,0,0] 2 3 (by decide)
    (by norm_num [Maximum_four]) (by norm_num [Maximum_four])
    (by norm_num [lin_four,outwardRows]) (by norm_num [lin_four,outwardRows])
  norm_num [lin_four,outwardRows] at hc hb haa
  exact ha (by linarith only [hsum,hc,hb,haa])

#print axioms outward_fork_excluded
end MaxCaterpillar.Fiber.Count65.TwoRoots
