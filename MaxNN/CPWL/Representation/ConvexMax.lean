import MaxNN.CPWL.Representation.ConvexMax.Support
import MaxNN.CPWL.Representation.ConvexMax.FullDim
import MaxNN.CPWL.Closure
import MaxNN.Core.Max
import MaxNN.Core.Class

/-!
# Convex CPWL functions are maxima of finitely many affine functions

Stage (ii) of the hinging-representation programme (`work/DFS_LOG.md`, branch group
CPWL): `isMaxOfAffine_of_convexOn_cpwl` — a **convex** CPWL function is the pointwise
maximum of finitely many affine functions.  Proof: by the Baire brick
(`ConvexMax/FullDim.lean`) every point lies in a full-dimensional piece, and by the
support brick (`ConvexMax/Support.lean`) the affine function of a full-dimensional
piece is a global minorant; thin pieces are discarded by re-using the affine function
of a fixed full-dimensional piece.

Converses (`convexOn_of_isMaxOfAffine`, `mem_cpwl_of_isMaxOfAffine`) make this an
exact characterization:  `IsMaxOfAffine d f ↔ f ∈ CPWL d ∧ ConvexOn ℝ univ f`.

Corollary chain into the network world: a maximum of `r+1` affine functions is
computable with `r` hidden layers (`maxOfAffine_mem_reluClass`), hence **every convex
CPWL function is computed exactly by some ReLU network**
(`exists_mem_reluClass_of_convexOn_cpwl`) — the converse inclusion being
`reluClass_subset_cpwl` (`MaxNN/CPWL/Networks.lean`).

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-- `f` is a pointwise maximum of finitely many (at least one) affine functions. -/
def IsMaxOfAffine (d : ℕ) (f : (Fin d → ℝ) → ℝ) : Prop :=
  ∃ (r : ℕ) (g : Fin (r + 1) → AffineFn d),
    ∀ x, f x = MAX (r + 1) fun t => (g t).eval x

/-- **Stage (ii) of the representation theorem.**  A convex CPWL function is the
pointwise maximum of finitely many affine functions — namely, of the affine functions
attached to the full-dimensional pieces of any witness. -/
theorem isMaxOfAffine_of_convexOn_cpwl {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : f ∈ CPWL d) (hconv : ConvexOn ℝ Set.univ f) : IsMaxOfAffine d f := by
  classical
  obtain ⟨-, ⟨W⟩⟩ := hf
  obtain ⟨n, P, g, covers, agrees⟩ := W
  rcases n with _ | m
  · obtain ⟨i, -⟩ := covers 0
    exact i.elim0
  · -- a fixed full-dimensional piece, to re-use on thin pieces
    obtain ⟨i₀, -, hi₀⟩ := exists_mem_interior_nonempty_of_covers P covers 0
    refine ⟨m, fun t => if (interior (P t).carrier).Nonempty then g t else g i₀, ?_⟩
    intro x
    have hminor : ∀ t : Fin (m + 1),
        (if (interior (P t).carrier).Nonempty then g t else g i₀).eval x ≤ f x := by
      intro t
      by_cases h : (interior (P t).carrier).Nonempty
      · rw [if_pos h]
        obtain ⟨z, hz⟩ := h
        exact AffineFn.le_of_convexOn_of_eqOn_open hconv isOpen_interior hz
          (fun w hw => agrees t w (interior_subset hw)) x
      · rw [if_neg h]
        obtain ⟨z, hz⟩ := hi₀
        exact AffineFn.le_of_convexOn_of_eqOn_open hconv isOpen_interior hz
          (fun w hw => agrees i₀ w (interior_subset hw)) x
    obtain ⟨i, hmem, hint⟩ := exists_mem_interior_nonempty_of_covers P covers x
    refine le_antisymm ?_ (MAX_le fun t => hminor t)
    have e : f x = (if (interior (P i).carrier).Nonempty then g i else g i₀).eval x := by
      rw [if_pos hint]
      exact agrees i x hmem
    rw [e]
    exact le_MAX (m + 1)
      (fun t => (if (interior (P t).carrier).Nonempty then g t else g i₀).eval x) i

/-! ## Converses: maxima of affine functions are convex and CPWL -/

/-- An affine function is convex. -/
theorem AffineFn.convexOn_eval {d : ℕ} (g : AffineFn d) :
    ConvexOn ℝ Set.univ g.eval :=
  ⟨convex_univ, fun x _ y _ _a _b _ _ hab => le_of_eq (g.eval_convexComb hab x y)⟩

/-- A pointwise maximum of finitely many affine functions is convex. -/
theorem convexOn_of_isMaxOfAffine {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : IsMaxOfAffine d f) : ConvexOn ℝ Set.univ f := by
  obtain ⟨r, g, hrep⟩ := hf
  have e : f = fun x => MAX (r + 1) fun t => (g t).eval x := funext hrep
  rw [e]
  clear e hrep f
  induction r with
  | zero =>
    have e1 : (fun x : Fin d → ℝ => MAX 1 fun t => (g t).eval x)
        = fun x => (g 0).eval x := funext fun x => MAX_one _
    rw [e1]
    exact (g 0).convexOn_eval
  | succ r ih =>
    have e1 : (fun x : Fin d → ℝ => MAX (r + 2) fun t => (g t).eval x)
        = fun x => max (MAX (r + 1) fun t => (g t.castSucc).eval x)
            ((g (Fin.last (r + 1))).eval x) :=
      funext fun x => MAX_succ (r + 1) _
    rw [e1]
    exact ConvexOn.sup (ih fun t => g t.castSucc) (g (Fin.last (r + 1))).convexOn_eval

/-- A pointwise maximum of finitely many affine functions is CPWL. -/
theorem mem_cpwl_of_isMaxOfAffine {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : IsMaxOfAffine d f) : f ∈ CPWL d := by
  obtain ⟨r, g, hrep⟩ := hf
  have e : f = fun x => MAX (r + 1) fun t => (g t).eval x := funext hrep
  rw [e]
  clear e hrep f
  induction r with
  | zero =>
    have e1 : (fun x : Fin d → ℝ => MAX 1 fun t => (g t).eval x)
        = fun x => (g 0).eval x := funext fun x => MAX_one _
    rw [e1]
    exact affineFn_mem_cpwl (g 0)
  | succ r ih =>
    have e1 : (fun x : Fin d → ℝ => MAX (r + 2) fun t => (g t).eval x)
        = fun x => max (MAX (r + 1) fun t => (g t.castSucc).eval x)
            ((g (Fin.last (r + 1))).eval x) :=
      funext fun x => MAX_succ (r + 1) _
    rw [e1]
    exact max_mem_cpwl (ih fun t => g t.castSucc) (affineFn_mem_cpwl (g (Fin.last (r + 1))))

/-- The exact characterization: the maxima of finitely many affine functions are
precisely the convex CPWL functions. -/
theorem isMaxOfAffine_iff_convexOn_cpwl {d : ℕ} {f : (Fin d → ℝ) → ℝ} :
    IsMaxOfAffine d f ↔ f ∈ CPWL d ∧ ConvexOn ℝ Set.univ f :=
  ⟨fun h => ⟨mem_cpwl_of_isMaxOfAffine h, convexOn_of_isMaxOfAffine h⟩,
    fun h => isMaxOfAffine_of_convexOn_cpwl h.1 h.2⟩

/-! ## Into the network world -/

/-- A maximum of `r+1` affine functions is computable with `r` hidden layers. -/
theorem maxOfAffine_mem_reluClass {d : ℕ} :
    ∀ (r : ℕ) (g : Fin (r + 1) → AffineFn d),
      (fun x => MAX (r + 1) fun t => (g t).eval x) ∈ ReLUClass d r := by
  intro r
  induction r with
  | zero =>
    intro g
    have e : (fun x : Fin d → ℝ => MAX 1 fun t => (g t).eval x)
        = fun x => (g 0).eval x := funext fun x => MAX_one _
    rw [e]
    exact affine_mem_reluClass (g 0).a (g 0).c
  | succ r ih =>
    intro g
    have e : (fun x : Fin d → ℝ => MAX (r + 2) fun t => (g t).eval x)
        = fun x => max (MAX (r + 1) fun t => (g t.castSucc).eval x)
            ((g (Fin.last (r + 1))).eval x) :=
      funext fun x => MAX_succ (r + 1) _
    rw [e]
    exact max_mem_reluClass (ih fun t => g t.castSucc)
      (reluClass_mono (Nat.zero_le r)
        (affine_mem_reluClass (g (Fin.last (r + 1))).a (g (Fin.last (r + 1))).c))

/-- A maximum of finitely many affine functions is exactly ReLU-computable. -/
theorem exists_mem_reluClass_of_isMaxOfAffine {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : IsMaxOfAffine d f) : ∃ k, f ∈ ReLUClass d k := by
  obtain ⟨r, g, hrep⟩ := hf
  refine ⟨r, ?_⟩
  have e : f = fun x => MAX (r + 1) fun t => (g t).eval x := funext hrep
  rw [e]
  exact maxOfAffine_mem_reluClass r g

/-- **Every convex CPWL function is computed exactly by some ReLU network.**
(The converse inclusion is `reluClass_subset_cpwl`.) -/
theorem exists_mem_reluClass_of_convexOn_cpwl {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : f ∈ CPWL d) (hconv : ConvexOn ℝ Set.univ f) : ∃ k, f ∈ ReLUClass d k :=
  exists_mem_reluClass_of_isMaxOfAffine (isMaxOfAffine_of_convexOn_cpwl hf hconv)

end MaxNN
