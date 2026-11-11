import MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups.Decomposition
import MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups.Erasure
import MaxCaterpillar.Fiber.Count65.Paired.SplitChord
import MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups.PairReduction
import MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups.SignedChord
import MaxCaterpillar.Fiber.Count65.Paired.PairNormalization

/-! # Actual split attachment of the no-crossing quadrant branch

The source is an ordinary physical network. The selected second rows are
genuine coefficient combinations of two globally nonnegative affine feature
forms. All unselected rows are arbitrary spectators. Row classification is
derived from the unrestricted quadrant fit, not assumed as attachment.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups

open BigOperators Absorption

noncomputable def localWeights {k : ℕ} (d : Fin k → ℝ) (S : Finset (Fin k)) : Fin k → ℝ :=
  fun i => if i ∈ S then d i else 0

theorem localWeights_sum {k : ℕ} (d f : Fin k → ℝ) (S : Finset (Fin k)) :
    (∑ i, localWeights d S i*f i) = ∑ i in S, d i*f i := by
  have hfilter : Finset.univ.filter (fun i => i ∈ S) = S := by ext i; simp
  unfold localWeights
  simp only [ite_mul,zero_mul]
  rw [← Finset.sum_filter,hfilter]

theorem localWeights_crossing_sum {k : ℕ} (a b d f : Fin k → ℝ) (S : Finset (Fin k)) :
    (∑ i in crossingSlots a b, localWeights d S i*f i) =
      ∑ i in S.filter (fun i => a i*b i < 0), d i*f i := by
  classical
  have hg : (crossingSlots a b).filter (fun i => i ∈ S) =
      S.filter (fun i => a i*b i < 0) := by
    ext i
    simp [crossingSlots,and_comm]
  rw [← hg]
  symm
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hi : i ∈ S <;> simp [localWeights,hi]

theorem localWeights_knot_sum {k : ℕ} (a b d f : Fin k → ℝ)
    (S : Finset (Fin k)) (τ : ℝ) :
    (∑ i in knotGroup a b τ, localWeights d S i*f i) =
      ∑ i in S.filter (fun i => a i*τ+b i = 0), d i*f i := by
  classical
  have hg : (knotGroup a b τ).filter (fun i => i ∈ S) =
      S.filter (fun i => a i*τ+b i = 0) := by
    ext i
    simp [knotGroup,and_comm]
  rw [← hg]
  symm
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hi : i ∈ S <;> simp [localWeights,hi]

theorem localWeights_fit {k : ℕ} (a b d : Fin k → ℝ) (S : Finset (Fin k))
    (hfit : ∀ Q R : ℝ, 0 ≤ Q → 0 ≤ R →
      (∑ i in S, d i*max 0 (a i*Q+b i*R)) = Q-R) :
    ∀ Q R : ℝ, 0 ≤ Q → 0 ≤ R →
      (∑ i, localWeights d S i*max 0 (a i*Q+b i*R)) = Q-R := by
  intro Q R hQ hR
  have hfilter : Finset.univ.filter (fun i => i ∈ S) = S := by ext i; simp
  have hsum : (∑ i, localWeights d S i*max 0 (a i*Q+b i*R)) =
      ∑ i in S, d i*max 0 (a i*Q+b i*R) := by
    unfold localWeights
    simp only [ite_mul,zero_mul]
    rw [← Finset.sum_filter,hfilter]
  rw [hsum]
  exact hfit Q R hQ hR

theorem coefficient_preact {N m k : ℕ} (net : Network N m k)
    (Qrow Rrow : Fin m → ℝ) (Qbias Rbias : ℝ) (a b : Fin k → ℝ)
    (i : Fin k) (hrow : ∀ j, net.W₂ i j = a i*Qrow j+b i*Rrow j)
    (hbias : net.b₂ i = a i*Qbias+b i*Rbias) (x : Point N) :
    preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x =
      a i*preact net.W₁ net.b₁ Qrow Qbias x+
        b i*preact net.W₁ net.b₁ Rrow Rbias x := by
  simp only [preact,hrow,hbias,add_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

/-- The no-effective-crossing branch reaches a literal physical split target.
The result selects its positive and negative output slots from the source;
every other selected row and bias becomes zero. -/
theorem no_crossing_split_attachment {N m k : ℕ} [NeZero N]
    (net : Network N m k) (S : Finset (Fin k))
    (Qrow Rrow : Fin m → ℝ) (Qbias Rbias : ℝ) (a b : Fin k → ℝ)
    (hrow : ∀ i ∈ S, ∀ j, net.W₂ i j = a i*Qrow j+b i*Rrow j)
    (hbias : ∀ i ∈ S, net.b₂ i = a i*Qbias+b i*Rbias)
    (hQ : ∀ x, 0 ≤ preact net.W₁ net.b₁ Qrow Qbias x)
    (hR : ∀ x, 0 ≤ preact net.W₁ net.b₁ Rrow Rbias x)
    (hquadrant : ∀ Q R : ℝ, 0 ≤ Q → 0 ≤ R →
      (∑ i in S, net.w₃ i*max 0 (a i*Q+b i*R)) = Q-R)
    (hno : ∀ i ∈ S, net.w₃ i ≠ 0 → ¬ a i*b i < 0)
    (hnet : ∀ x, net.eval x = Maximum N x) :
    ∃ p n : Fin k, p ∈ S ∧ n ∈ S ∧ p ≠ n ∧ 0 < net.w₃ p ∧ net.w₃ n < 0 ∧
      JoinedIn (ExactSet N m k) net
        (withSecondRows net (splitTargetRows net Qrow Rrow S p n)
          (splitTargetBiases net Qbias Rbias S p n)) := by
  classical
  let d := localWeights net.w₃ S
  have hfit := localWeights_fit a b net.w₃ S hquadrant
  have hnox : ∀ i, d i ≠ 0 → ¬ a i*b i < 0 := by
    intro i hdi
    by_cases hi : i ∈ S
    · exact hno i hi (by simpa only [d,localWeights,if_pos hi] using hdi)
    · exact False.elim (hdi (by simp [d,localWeights,hi]))
  rcases no_crossing_active_signs a b d hnox hfit with
    ⟨⟨p,hdp,hap,hbp⟩,⟨n,hdn,han,hbn⟩⟩
  have hpS : p ∈ S := by
    by_contra hp
    simp [d,localWeights,hp] at hdp
  have hnS : n ∈ S := by
    by_contra hn
    simp [d,localWeights,hn] at hdn
  have hdp' : 0 < net.w₃ p := by simpa only [d,localWeights,if_pos hpS] using hdp
  have hdn' : net.w₃ n < 0 := by simpa only [d,localWeights,if_pos hnS] using hdn
  have hpn : p ≠ n := by intro h; rw [h] at hdp'; linarith only [hdp',hdn']
  have hpnonneg : ∀ x, 0 ≤ preact net.W₁ net.b₁ (net.W₂ p) (net.b₂ p) x := by
    intro x
    rw [coefficient_preact net Qrow Rrow Qbias Rbias a b p (hrow p hpS) (hbias p hpS) x]
    exact add_nonneg (mul_nonneg hap.le (hQ x)) (mul_nonneg hbp (hR x))
  have hnnonneg : ∀ x, 0 ≤ preact net.W₁ net.b₁ (net.W₂ n) (net.b₂ n) x := by
    intro x
    rw [coefficient_preact net Qrow Rrow Qbias Rbias a b n (hrow n hnS) (hbias n hnS) x]
    exact add_nonneg (mul_nonneg han (hQ x)) (mul_nonneg hbn.le (hR x))
  have hlocal : ∀ x, (∑ i in S, net.w₃ i*relu
      (preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x)) =
      preact net.W₁ net.b₁ Qrow Qbias x-preact net.W₁ net.b₁ Rrow Rbias x := by
    intro x
    calc
      _ = ∑ i in S, net.w₃ i*max 0 (a i*preact net.W₁ net.b₁ Qrow Qbias x+
          b i*preact net.W₁ net.b₁ Rrow Rbias x) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [coefficient_preact net Qrow Rrow Qbias Rbias a b i (hrow i hi) (hbias i hi) x]
        rfl
      _ = _ := hquadrant _ _ (hQ x) (hR x)
  exact ⟨p,n,hpS,hnS,hpn,hdp',hdn',
    splitChord_joinedIn_exact net Qrow Rrow Qbias Rbias S p n hpS hnS hpn
      hdp' hdn' hpnonneg hnnonneg hQ hR hlocal hnet⟩

noncomputable def eraseCrossingNet {N m k : ℕ} (net : Network N m k)
    (S : Finset (Fin k)) (a b : Fin k → ℝ) : Network N m k :=
  withOutput net (eraseClusterOutput net.w₃ (S.filter (fun i => a i*b i < 0))) net.b₃

/-- Complete physical attachment of the branch in which every crossing ray
has zero surviving coefficient. All crossings are erased together, and the
remaining exact representation is joined to the literal split target. -/
theorem zero_crossing_groups_split_attachment {N m k : ℕ} [NeZero N]
    (net : Network N m k) (S : Finset (Fin k))
    (Qrow Rrow : Fin m → ℝ) (Qbias Rbias : ℝ) (a b : Fin k → ℝ)
    (hrow : ∀ i ∈ S, ∀ j, net.W₂ i j = a i*Qrow j+b i*Rrow j)
    (hbias : ∀ i ∈ S, net.b₂ i = a i*Qbias+b i*Rbias)
    (hQ : ∀ x, 0 ≤ preact net.W₁ net.b₁ Qrow Qbias x)
    (hR : ∀ x, 0 ≤ preact net.W₁ net.b₁ Rrow Rbias x)
    (hquadrant : ∀ Q R : ℝ, 0 ≤ Q → 0 ≤ R →
      (∑ i in S, net.w₃ i*max 0 (a i*Q+b i*R)) = Q-R)
    (hzero : ∀ τ ∈ knotLocations a b,
      groupCoefficient a b (localWeights net.w₃ S) τ = 0)
    (hnet : ∀ x, net.eval x = Maximum N x) :
    let mid := eraseCrossingNet net S a b
    ∃ p n : Fin k, p ∈ S ∧ n ∈ S ∧ p ≠ n ∧ 0 < mid.w₃ p ∧ mid.w₃ n < 0 ∧
      JoinedIn (ExactSet N m k) net
        (withSecondRows mid (splitTargetRows mid Qrow Rrow S p n)
          (splitTargetBiases mid Qbias Rbias S p n)) := by
  classical
  let g := S.filter (fun i => a i*b i < 0)
  let mid := eraseCrossingNet net S a b
  have hgsub : ∀ i ∈ g, i ∈ S := fun i hi => (Finset.mem_filter.mp hi).1
  have hmasked := localWeights_fit a b net.w₃ S hquadrant
  have hgzero (Q R : ℝ) : (∑ i in g, net.w₃ i*max 0 (a i*Q+b i*R)) = 0 := by
    have h := all_zero_crossing_groups_cancel a b (localWeights net.w₃ S) hmasked hzero Q R
    rw [localWeights_crossing_sum] at h
    exact h
  have hphysical : ∀ x, (∑ i in g, net.w₃ i*relu
      (preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x)) = 0 := by
    intro x
    calc
      _ = ∑ i in g, net.w₃ i*max 0 (a i*preact net.W₁ net.b₁ Qrow Qbias x+
          b i*preact net.W₁ net.b₁ Rrow Rbias x) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [coefficient_preact net Qrow Rrow Qbias Rbias a b i
          (hrow i (hgsub i hi)) (hbias i (hgsub i hi)) x]
        rfl
      _ = 0 := hgzero _ _
  have hpath : JoinedIn (ExactSet N m k) net mid :=
    eraseCancelingCluster_joinedIn_exact ⟨net,hnet⟩ g hphysical
  have hquadmid : ∀ Q R : ℝ, 0 ≤ Q → 0 ≤ R →
      (∑ i in S, mid.w₃ i*max 0 (a i*Q+b i*R)) = Q-R := by
    intro Q R hQ' hR'
    have hzeromask : (∑ i in g, localWeights net.w₃ S i*max 0 (a i*Q+b i*R)) = 0 := by
      convert hgzero Q R using 1
      apply Finset.sum_congr rfl
      intro i hi
      simp only [localWeights,if_pos (hgsub i hi)]
    have hcommute : localWeights mid.w₃ S = eraseClusterOutput (localWeights net.w₃ S) g := by
      funext i
      change (if i ∈ S then (if i ∈ g then 0 else net.w₃ i) else 0) =
        (if i ∈ g then 0 else if i ∈ S then net.w₃ i else 0)
      by_cases hi : i ∈ S <;> by_cases hig : i ∈ g <;>
        simp only [hi,hig,if_true,if_false]
    rw [← localWeights_sum mid.w₃ (fun i => max 0 (a i*Q+b i*R)) S,hcommute,
      eraseClusterOutput_sum _ _ g hzeromask]
    exact hmasked Q R hQ' hR'
  have hnomid : ∀ i ∈ S, mid.w₃ i ≠ 0 → ¬ a i*b i < 0 := by
    intro i hi hdi hc
    have hig : i ∈ g := Finset.mem_filter.mpr ⟨hi,hc⟩
    exact hdi (by simp only [mid,eraseCrossingNet,withOutput,eraseClusterOutput,if_pos hig])
  rcases no_crossing_split_attachment mid S Qrow Rrow Qbias Rbias a b hrow hbias
    hQ hR hquadmid hnomid hpath.target_mem with ⟨p,n,hp,hn,hpn,hdp,hdn,hend⟩
  exact ⟨p,n,hp,hn,hpn,hdp,hdn,hpath.trans hend⟩

/-- A surviving crossing ray gives an actual signed-baseline attachment.
Only one ray group is concentrated; the signed chord absorbs every remaining
selected gate simultaneously. There is no width bound or knot-count casework. -/
theorem surviving_crossing_signed_attachment {N m k : ℕ} [NeZero N]
    (net : Network N m k) (S : Finset (Fin k))
    (Qrow Rrow : Fin m → ℝ) (Qbias Rbias : ℝ) (a b : Fin k → ℝ)
    (hrow : ∀ i ∈ S, ∀ j, net.W₂ i j = a i*Qrow j+b i*Rrow j)
    (hbias : ∀ i ∈ S, net.b₂ i = a i*Qbias+b i*Rbias)
    (hQ : ∀ x, 0 ≤ preact net.W₁ net.b₁ Qrow Qbias x)
    (hR : ∀ x, 0 ≤ preact net.W₁ net.b₁ Rrow Rbias x)
    (hquadrant : ∀ Q R : ℝ, 0 ≤ Q → 0 ≤ R →
      (∑ i in S, net.w₃ i*max 0 (a i*Q+b i*R)) = Q-R)
    (τ : ℝ) (hτ : 0 < τ)
    (hP : groupCoefficient a b (localWeights net.w₃ S) τ ≠ 0)
    (hnet : ∀ x, net.eval x = Maximum N x) :
    ∃ (mid : Network N m k) (p n : Fin k), p ∈ S ∧ n ∈ S ∧ p ≠ n ∧
      mid.W₁ = net.W₁ ∧ mid.b₁ = net.b₁ ∧ mid.b₃ = net.b₃ ∧
      mid.w₃ p = 1 ∧ mid.w₃ n = -1 ∧
      (∀ i ∉ S, mid.W₂ i = net.W₂ i ∧ mid.b₂ i = net.b₂ i ∧ mid.w₃ i = net.w₃ i) ∧
      JoinedIn (ExactSet N m k) net
        (withSecondRows mid (signedChordRows mid S p n (fun j => Qrow j-Rrow j))
          (signedChordBiases mid S p n (Qbias-Rbias))) := by
  classical
  let g := S.filter (fun i => a i*τ+b i = 0)
  let C := ∑ i in g, net.w₃ i*max 0 (a i)
  let H := fun x => preact net.W₁ net.b₁ Qrow Qbias x-τ*preact net.W₁ net.b₁ Rrow Rbias x
  have hgS : g ⊆ S := fun i hi => (Finset.mem_filter.mp hi).1
  have hmasked := localWeights_fit a b net.w₃ S hquadrant
  have hC : C = groupCoefficient a b (localWeights net.w₃ S) τ :=
    (localWeights_knot_sum a b net.w₃ (fun i => max 0 (a i)) S τ).symm
  have hC0 : C ≠ 0 := by rw [hC]; exact hP
  rcases knotGroup_nonzero_has_opposite_slots a b (localWeights net.w₃ S) τ hτ hmasked hP with
    ⟨p,n,hpk,hnk,hdp,hdn,hap,han,hpn⟩
  have hpS : p ∈ S := by by_contra h; simp [localWeights,h] at hdp
  have hnS : n ∈ S := by by_contra h; simp [localWeights,h] at hdn
  have hpg : p ∈ g := Finset.mem_filter.mpr ⟨hpS,(Finset.mem_filter.mp hpk).2⟩
  have hng : n ∈ g := Finset.mem_filter.mpr ⟨hnS,(Finset.mem_filter.mp hnk).2⟩
  have hjump : (∑ i in g, net.w₃ i*|a i|) = 0 := by
    have h := knotGroup_jump_zero a b (localWeights net.w₃ S) τ hτ hmasked
    rw [localWeights_knot_sum] at h
    exact h
  have hpre : ∀ i ∈ g, ∀ x, preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x = a i*H x := by
    intro i hi x
    have hiz := (Finset.mem_filter.mp hi).2
    have hib : b i = -(a i*τ) := by linarith only [hiz]
    rw [coefficient_preact net Qrow Rrow Qbias Rbias a b i (hrow i (hgS hi)) (hbias i (hgS hi)) x]
    dsimp [H]
    rw [hib]
    ring
  let sparse := withOutput net (sparsePairOutput net.w₃ g p n C (a p) (a n)) net.b₃
  have hpath : JoinedIn (ExactSet N m k) net sparse :=
    sparse_group_pair_joinedIn_exact net g a p n hpg hng hap han hjump H hpre hnet
  have hep : sparse.w₃ p = C/a p := sparsePairOutput_pos _ _ _ _ _ _ _ hpg hpn
  have hen : sparse.w₃ n = C/a n := sparsePairOutput_neg _ _ _ _ _ _ _ hng hpn
  have hcancel : ∀ x, sparse.w₃ p*preact sparse.W₁ sparse.b₁ (sparse.W₂ p) (sparse.b₂ p) x =
      sparse.w₃ n*preact sparse.W₁ sparse.b₁ (sparse.W₂ n) (sparse.b₂ n) x :=
    sparse_group_pair_weighted_preact net g a p n hpg hng hap han C H hpre
  have hlocal (x : Point N) : (∑ i in S, sparse.w₃ i*relu
      (preact sparse.W₁ sparse.b₁ (sparse.W₂ i) (sparse.b₂ i) x)) =
      preact sparse.W₁ sparse.b₁ (fun j => Qrow j-Rrow j) (Qbias-Rbias) x := by
    change (∑ i in S, sparsePairOutput net.w₃ g p n C (a p) (a n) i*
      relu (preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x)) =
      preact net.W₁ net.b₁ (fun j => Qrow j-Rrow j) (Qbias-Rbias) x
    rw [sparse_group_pair_sum_preserved net g S hgS a p n hpg hng hap han hjump H hpre x]
    have ht := preact_addmul net.W₁ net.b₁ Qrow Rrow Qbias Rbias (-1) x
    have ht' : preact net.W₁ net.b₁ (fun j => Qrow j-Rrow j) (Qbias-Rbias) x =
        preact net.W₁ net.b₁ Qrow Qbias x-preact net.W₁ net.b₁ Rrow Rbias x := by
      simpa only [neg_one_mul,sub_eq_add_neg] using ht
    rw [ht']
    calc
      _ = ∑ i in S, net.w₃ i*max 0 (a i*preact net.W₁ net.b₁ Qrow Qbias x+
          b i*preact net.W₁ net.b₁ Rrow Rbias x) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [coefficient_preact net Qrow Rrow Qbias Rbias a b i (hrow i hi) (hbias i hi) x]
        rfl
      _ = _ := hquadrant _ _ (hQ x) (hR x)
  have finish (u v : Fin k) (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
      (hdu : 0 < sparse.w₃ u) (hdv : sparse.w₃ v < 0)
      (hc : ∀ x, sparse.w₃ u*preact sparse.W₁ sparse.b₁ (sparse.W₂ u) (sparse.b₂ u) x =
        sparse.w₃ v*preact sparse.W₁ sparse.b₁ (sparse.W₂ v) (sparse.b₂ v) x) :
      ∃ (mid : Network N m k) (p n : Fin k), p ∈ S ∧ n ∈ S ∧ p ≠ n ∧
        mid.W₁ = net.W₁ ∧ mid.b₁ = net.b₁ ∧ mid.b₃ = net.b₃ ∧
        mid.w₃ p = 1 ∧ mid.w₃ n = -1 ∧
        (∀ i ∉ S, mid.W₂ i = net.W₂ i ∧ mid.b₂ i = net.b₂ i ∧ mid.w₃ i = net.w₃ i) ∧
        JoinedIn (ExactSet N m k) net
          (withSecondRows mid (signedChordRows mid S p n (fun j => Qrow j-Rrow j))
            (signedChordBiases mid S p n (Qbias-Rbias))) := by
    let mid := PairNormalization.normalizePair sparse u v
    have hnorm : JoinedIn (ExactSet N m k) sparse mid :=
      PairNormalization.normalizePair_joinedIn_exact ⟨sparse,hpath.target_mem⟩ u v hdu hdv
    have hmidp := PairNormalization.normalizePair_output_pos sparse u v hdu
    have hmidn := PairNormalization.normalizePair_output_neg sparse u v huv hdv
    have hneg := PairNormalization.normalizePair_preact_opposite sparse u v huv hc
    have hmidfit : ∀ x, (∑ i in S, mid.w₃ i*relu
        (preact mid.W₁ mid.b₁ (mid.W₂ i) (mid.b₂ i) x)) =
        preact mid.W₁ mid.b₁ (fun j => Qrow j-Rrow j) (Qbias-Rbias) x := by
      intro x
      exact (PairNormalization.normalizePair_sum_preserved sparse u v hdu hdv S x).trans (hlocal x)
    have hchord := signedChord_joinedIn_exact ⟨mid,hnorm.target_mem⟩ S u v hu hv huv
      hmidp hmidn hneg (fun j => Qrow j-Rrow j) (Qbias-Rbias) hmidfit
    refine ⟨mid,u,v,hu,hv,huv,rfl,rfl,rfl,hmidp,hmidn,?_,(hpath.trans hnorm).trans hchord⟩
    intro i hi
    have hiu : i ≠ u := by rintro rfl; exact hi hu
    have hiv : i ≠ v := by rintro rfl; exact hi hv
    rcases PairNormalization.normalizePair_unselected sparse u v i hiu hiv with ⟨hwi,hbi,hdi⟩
    refine ⟨hwi,hbi,?_⟩
    calc
      _ = sparse.w₃ i := hdi
      _ = net.w₃ i := sparsePairOutput_spectator net.w₃ g p n i C (a p) (a n) hpg hng
        (fun hig => hi (hgS hig))
  rcases lt_or_gt_of_ne hC0 with hCn | hCp
  · apply finish n p hnS hpS (Ne.symm hpn)
    · rw [hen]; exact div_pos_of_neg_of_neg hCn han
    · rw [hep]; exact div_neg_of_neg_of_pos hCn hap
    · intro x; exact (hcancel x).symm
  · apply finish p n hpS hnS hpn
    · rw [hep]; exact div_pos hCp hap
    · rw [hen]; exact div_neg_of_pos_of_neg hCp han
    · exact hcancel

/-- An actual physical path to a literal signed baseline in two selected
slots, with all other selected incoming rows and biases zero at the endpoint. -/
def SignedBaselineAttached {N m k : ℕ} [NeZero N] (net : Network N m k)
    (S : Finset (Fin k)) (Qrow Rrow : Fin m → ℝ) (Qbias Rbias : ℝ) : Prop :=
  ∃ (mid : Network N m k) (p n : Fin k), p ∈ S ∧ n ∈ S ∧ p ≠ n ∧
    mid.W₁ = net.W₁ ∧ mid.b₁ = net.b₁ ∧ mid.b₃ = net.b₃ ∧
    mid.w₃ p = 1 ∧ mid.w₃ n = -1 ∧
    (∀ i ∉ S, mid.W₂ i = net.W₂ i ∧ mid.b₂ i = net.b₂ i ∧ mid.w₃ i = net.w₃ i) ∧
    JoinedIn (ExactSet N m k) net
      (withSecondRows mid (signedChordRows mid S p n (fun j => Qrow j-Rrow j))
        (signedChordBiases mid S p n (Qbias-Rbias)))

/-- An actual physical path to a literal split baseline after the cancelled
crossing outputs are erased. The two surviving outputs have opposite signs. -/
def SplitBaselineAttached {N m k : ℕ} [NeZero N] (net : Network N m k)
    (S : Finset (Fin k)) (Qrow Rrow : Fin m → ℝ) (Qbias Rbias : ℝ)
    (a b : Fin k → ℝ) : Prop :=
  let mid := eraseCrossingNet net S a b
  ∃ p n : Fin k, p ∈ S ∧ n ∈ S ∧ p ≠ n ∧ 0 < mid.w₃ p ∧ mid.w₃ n < 0 ∧
    JoinedIn (ExactSet N m k) net
      (withSecondRows mid (splitTargetRows mid Qrow Rrow S p n)
        (splitTargetBiases mid Qbias Rbias S p n))

/-- Finite homogeneous quadrant classification realized by paths of ordinary
physical coefficients. The input is an unrestricted exact quadrant identity,
coefficientwise physical row/bias formulas, and ordinary all-input exactness.
The conclusion is an actual signed or split baseline attachment. -/
theorem quadrant_baseline_attachment {N m k : ℕ} [NeZero N]
    (net : Network N m k) (S : Finset (Fin k))
    (Qrow Rrow : Fin m → ℝ) (Qbias Rbias : ℝ) (a b : Fin k → ℝ)
    (hrow : ∀ i ∈ S, ∀ j, net.W₂ i j = a i*Qrow j+b i*Rrow j)
    (hbias : ∀ i ∈ S, net.b₂ i = a i*Qbias+b i*Rbias)
    (hQ : ∀ x, 0 ≤ preact net.W₁ net.b₁ Qrow Qbias x)
    (hR : ∀ x, 0 ≤ preact net.W₁ net.b₁ Rrow Rbias x)
    (hquadrant : ∀ Q R : ℝ, 0 ≤ Q → 0 ≤ R →
      (∑ i in S, net.w₃ i*max 0 (a i*Q+b i*R)) = Q-R)
    (hnet : ∀ x, net.eval x = Maximum N x) :
    SignedBaselineAttached net S Qrow Rrow Qbias Rbias ∨
      SplitBaselineAttached net S Qrow Rrow Qbias Rbias a b := by
  classical
  by_cases hsurvives : ∃ τ ∈ knotLocations a b,
      groupCoefficient a b (localWeights net.w₃ S) τ ≠ 0
  · rcases hsurvives with ⟨τ,hτ,hP⟩
    exact Or.inl (surviving_crossing_signed_attachment net S Qrow Rrow Qbias Rbias a b
      hrow hbias hQ hR hquadrant τ (knotLocations_positive a b τ hτ) hP hnet)
  · apply Or.inr
    apply zero_crossing_groups_split_attachment net S Qrow Rrow Qbias Rbias a b
      hrow hbias hQ hR hquadrant _ hnet
    intro τ hτ
    by_contra hP
    exact hsurvives ⟨τ,hτ,hP⟩

end MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups
