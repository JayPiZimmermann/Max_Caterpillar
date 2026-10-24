import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Powerset

/-!
# Star covers

Every finite graph has a *star cover* of its non-isolated vertices: a map `ctr` sending each
non-isolated vertex to the centre of its star, every non-centre being adjacent to its centre
and every centre having a further vertex of its star.  Proof: a minimum edge cover has an
endpoint of degree one on every edge (otherwise the edge could be dropped), so its components
are stars (`research/sN/simplify/exponential.md`, step S6).
-/

open Finset

namespace MaxCaterpillar.Simplify

namespace StarCover

open Classical

variable {N : ℕ}

/-- The edges of `E` at `v`. -/
noncomputable def inc (E : Finset (Fin N × Fin N)) (v : Fin N) : Finset (Fin N × Fin N) :=
  E.filter fun e => e.1 = v ∨ e.2 = v

/-- The other endpoint of `e` seen from `v`. -/
def other (e : Fin N × Fin N) (v : Fin N) : Fin N := if e.1 = v then e.2 else e.1

/-- The other endpoint of some edge at `v`. -/
noncomputable def oth (E : Finset (Fin N × Fin N)) (v : Fin N) : Fin N :=
  if h : (inc E v).Nonempty then other h.choose v else v

/-- The centre of the star of `v`. -/
noncomputable def ctr (E : Finset (Fin N × Fin N)) (v : Fin N) : Fin N :=
  if (inc E v).card = 1 then (if (inc E (oth E v)).card = 1 then min v (oth E v) else oth E v)
  else v

theorem mem_inc {E : Finset (Fin N × Fin N)} {v : Fin N} {e : Fin N × Fin N} :
    e ∈ inc E v ↔ e ∈ E ∧ (e.1 = v ∨ e.2 = v) := mem_filter

theorem other_spec {e : Fin N × Fin N} {v : Fin N} (hne : e.1 ≠ e.2) (hv : e.1 = v ∨ e.2 = v) :
    other e v ≠ v ∧ (e.1 = other e v ∨ e.2 = other e v) ∧ other e (other e v) = v ∧
      ((e.1 = v ∧ e.2 = other e v) ∨ (e.2 = v ∧ e.1 = other e v)) := by
  rcases hv with h | h
  · have h1 : other e v = e.2 := if_pos h
    have h2 : other e e.2 = e.1 := if_neg hne
    rw [h1, h2, ← h]
    exact ⟨hne.symm, Or.inr rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · have h1 : other e v = e.1 := if_neg (by rw [← h]; exact hne)
    have h2 : other e e.1 = e.2 := if_pos rfl
    rw [h1, h2, ← h]
    exact ⟨hne, Or.inl rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩

theorem oth_eq {E : Finset (Fin N × Fin N)} {v : Fin N} {e : Fin N × Fin N}
    (h1 : (inc E v).card = 1) (he : e ∈ inc E v) : oth E v = other e v := by
  obtain ⟨a, ha⟩ := card_eq_one.mp h1
  have hn : (inc E v).Nonempty := ⟨e, he⟩
  have hc : hn.choose = a := mem_singleton.mp ((Finset.ext_iff.mp ha _).mp hn.choose_spec)
  have he' : e = a := mem_singleton.mp ((Finset.ext_iff.mp ha _).mp he)
  unfold oth
  rw [dif_pos hn, hc, he']

/-- **Star cover.** For a symmetric irreflexive relation `R` on `Fin N` there is `c` such
that for every non-isolated `v`: `c v` is non-isolated, `c (c v) = c v`,
`R (c v) v` unless `c v = v`, and every centre `v = c v` is the centre of another
non-isolated vertex. -/
theorem exists_starCover (R : Fin N → Fin N → Prop) (hsymm : ∀ u v, R u v → R v u)
    (hirr : ∀ v, ¬ R v v) :
    ∃ c : Fin N → Fin N, ∀ v, (∃ w, R v w) →
      (∃ w, R (c v) w) ∧ c (c v) = c v ∧ (c v ≠ v → R (c v) v) ∧
      (c v = v → ∃ w, w ≠ v ∧ (∃ x, R w x) ∧ c w = v) := by
  set Ep : Finset (Fin N × Fin N) := univ.filter fun e => R e.1 e.2 ∧ e.1 < e.2
  have hcovEp : ∀ v, (∃ w, R v w) → ∃ e ∈ Ep, e.1 = v ∨ e.2 = v := by
    rintro v ⟨w, hvw⟩
    have hne : v ≠ w := fun h => hirr v (h ▸ hvw)
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨(v, w), mem_filter.mpr ⟨mem_univ _, hvw, h⟩, Or.inl rfl⟩
    · exact ⟨(w, v), mem_filter.mpr ⟨mem_univ _, hsymm _ _ hvw, h⟩, Or.inr rfl⟩
  set fam := Ep.powerset.filter fun E => ∀ v, (∃ w, R v w) → ∃ e ∈ E, e.1 = v ∨ e.2 = v
  have hne : fam.Nonempty := ⟨Ep, mem_filter.mpr ⟨mem_powerset_self _, hcovEp⟩⟩
  obtain ⟨E, hEf, hEmin⟩ := fam.exists_min_image card hne
  obtain ⟨hEsub, hEcov⟩ := mem_filter.mp hEf
  rw [mem_powerset] at hEsub
  have hER : ∀ e ∈ E, R e.1 e.2 ∧ e.1 < e.2 := fun e he => (mem_filter.mp (hEsub he)).2
  -- every edge of a minimum cover has an endpoint of degree one
  have hkey : ∀ e ∈ E, (inc E e.1).card = 1 ∨ (inc E e.2).card = 1 := by
    intro e he
    by_contra hcon
    push_neg at hcon
    have hge : ∀ v, (e.1 = v ∨ e.2 = v) → 1 < (inc E v).card := by
      intro v hv
      have h1 : 1 ≤ (inc E v).card := card_pos.mpr ⟨e, mem_inc.mpr ⟨he, hv⟩⟩
      have h2 : (inc E v).card ≠ 1 := by
        rcases hv with h | h
        · rw [← h]; exact hcon.1
        · rw [← h]; exact hcon.2
      exact lt_of_le_of_ne h1 (Ne.symm h2)
    have hmem : E.erase e ∈ fam := by
      refine mem_filter.mpr ⟨mem_powerset.mpr ((erase_subset e E).trans hEsub), ?_⟩
      intro v hv
      obtain ⟨e', he', hve'⟩ := hEcov v hv
      by_cases hee : e' = e
      · subst hee
        obtain ⟨e'', he'', hne''⟩ := exists_ne_of_one_lt_card (hge v hve') e'
        obtain ⟨he''E, hv''⟩ := mem_inc.mp he''
        exact ⟨e'', mem_erase.mpr ⟨hne'', he''E⟩, hv''⟩
      · exact ⟨e', mem_erase.mpr ⟨hee, he'⟩, hve'⟩
    have h1 := hEmin _ hmem
    have h2 := card_erase_lt_of_mem he
    omega
  refine ⟨ctr E, fun v hv => ?_⟩
  obtain ⟨e, heE, hve⟩ := hEcov v hv
  have hev : e ∈ inc E v := mem_inc.mpr ⟨heE, hve⟩
  have hne12 : e.1 ≠ e.2 := ne_of_lt (hER e heE).2
  obtain ⟨hwv, hwe, how, hends⟩ := other_spec hne12 hve
  set w := other e v
  have hRw : R v w := by
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact (hER e heE).1
    · rw [← h1, ← h2]; exact hsymm _ _ (hER e heE).1
  have hew : e ∈ inc E w := mem_inc.mpr ⟨heE, hwe⟩
  by_cases h1 : (inc E v).card = 1
  · have hov : oth E v = w := oth_eq h1 hev
    by_cases h2 : (inc E w).card = 1
    · have how' : oth E w = v := by rw [oth_eq h2 hew, how]
      have hcv : ctr E v = min v w := by unfold ctr; rw [if_pos h1, hov, if_pos h2]
      have hcw : ctr E w = min v w := by
        unfold ctr; rw [if_pos h2, how', if_pos h1, min_comm]
      have hcases : ctr E v = v ∨ ctr E v = w := by
        rw [hcv]; rcases le_total v w with h | h
        · left; exact min_eq_left h
        · right; exact min_eq_right h
      refine ⟨?_, ?_, ?_, ?_⟩
      · rcases hcases with h | h <;> rw [h]
        · exact ⟨w, hRw⟩
        · exact ⟨v, hsymm _ _ hRw⟩
      · rcases hcases with h | h <;> rw [h]
        · exact h
        · rw [hcw]; exact hcv.symm.trans h
      · intro hne
        rcases hcases with h | h
        · exact absurd h hne
        · rw [h]; exact hsymm _ _ hRw
      · intro hcv'
        exact ⟨w, hwv, ⟨v, hsymm _ _ hRw⟩, by rw [hcw, ← hcv, hcv']⟩
    · have hcv : ctr E v = w := by unfold ctr; rw [if_pos h1, hov, if_neg h2]
      have hcw : ctr E w = w := by unfold ctr; rw [if_neg h2]
      refine ⟨by rw [hcv]; exact ⟨v, hsymm _ _ hRw⟩, by rw [hcv, hcw], fun _ => ?_, fun h => ?_⟩
      · rw [hcv]; exact hsymm _ _ hRw
      · rw [hcv] at h; exact absurd h hwv
  · have hcv : ctr E v = v := by unfold ctr; rw [if_neg h1]
    refine ⟨by rw [hcv]; exact hv, by rw [hcv, hcv], fun h => absurd hcv h, fun _ => ?_⟩
    -- the other end of an edge at a vertex of degree `≠ 1` has degree one
    have h2 : (inc E w).card = 1 := by
      have hk := hkey e heE
      rcases hends with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [ha, hb] at hk
        exact hk.resolve_left h1
      · rw [ha, hb] at hk
        exact hk.resolve_right h1
    have how' : oth E w = v := by rw [oth_eq h2 hew, how]
    refine ⟨w, hwv, ⟨v, hsymm _ _ hRw⟩, ?_⟩
    unfold ctr
    rw [if_pos h2, how', if_neg h1]

end StarCover

export StarCover (exists_starCover)

end MaxCaterpillar.Simplify
