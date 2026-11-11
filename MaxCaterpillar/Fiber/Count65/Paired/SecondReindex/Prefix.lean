import MaxCaterpillar.Fiber.Count65.Paired.SecondReindex

/-! Extend an ordered finite selection to an enumeration of physical slots. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired

theorem extend_second_prefix {s k : ℕ} (f : Fin s → Fin k) (hf : Function.Injective f) :
    ∃ e : Fin (s+(k-s)) ≃ Fin k, ∀ i : Fin s, e (Fin.castAdd (k-s) i) = f i := by
  classical
  have hsk : s ≤ k := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
  let S : Finset (Fin (s+(k-s))) := Finset.univ.image (Fin.castAdd (k-s) : Fin s → _)
  let F : Fin (s+(k-s)) → Fin k := Fin.addCases (m := s) (n := k-s)
    (motive := fun _ => Fin k) f (Fin.castLE (Nat.sub_le k s))
  have hF : Set.InjOn F S := by
    intro a ha b hb hab
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
    have hij : f i = f j := by simpa [F,Fin.addCases_left] using hab
    exact congrArg (Fin.castAdd (k-s)) (hf hij)
  obtain ⟨e,he⟩ := Finset.exists_equiv_extend_of_card_eq
    (α := Fin (s+(k-s))) (t := (Finset.univ : Finset (Fin k))) (s := S) (f := F)
    (by simp [Nat.add_sub_of_le hsk]) (Finset.subset_univ _) hF
  refine ⟨e.trans (Equiv.subtypeUnivEquiv (fun i : Fin k => Finset.mem_univ i)),?_⟩
  intro i
  have hi : Fin.castAdd (k-s) i ∈ S := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  simpa [F,Fin.addCases_left] using he (Fin.castAdd (k-s) i) hi

theorem ordered_three_second_equiv {k : ℕ} (p n z : Fin k)
    (hpn : p ≠ n) (hpz : p ≠ z) (hnz : n ≠ z) :
    ∃ e : Fin (3+(k-3)) ≃ Fin k,
      e (Fin.castAdd (k-3) 0) = p ∧
      e (Fin.castAdd (k-3) 1) = n ∧
      e (Fin.castAdd (k-3) 2) = z := by
  let f : Fin 3 → Fin k := ![p,n,z]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  obtain ⟨e,he⟩ := extend_second_prefix f hf
  exact ⟨e,he 0,he 1,he 2⟩

end MaxCaterpillar.Fiber.Count65.Paired
