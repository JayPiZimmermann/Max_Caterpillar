import MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment.Canonical
import MaxCaterpillar.Fiber.Count65.Paired.IndexedSignedSplit

/-! Every physical quadrant completion with a spare selected slot attaches to
a literal signed pair; all other selected incoming and outgoing entries vanish. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment
open BigOperators Absorption
variable {N m k : ℕ} [NeZero N]

theorem exists_spare_selected (S : Finset (Fin k)) (hS : 3≤S.card)
    (p n : Fin k) (hp : p∈S) (hn : n∈S) (hpn : p≠n) :
    ∃ z∈S,p≠z ∧ n≠z := by
  have hn' : n∈S.erase p := Finset.mem_erase.mpr ⟨Ne.symm hpn,hn⟩
  have hc1 := Finset.card_erase_add_one hp
  have hc2 := Finset.card_erase_add_one hn'
  have hpos : 0<((S.erase p).erase n).card := by
    by_contra h
    have hz := Nat.eq_zero_of_not_pos h
    rw [hz] at hc2
    linarith only [hc1,hc2,hS]
  obtain ⟨z,hz⟩ := Finset.card_pos.mp hpos
  rcases Finset.mem_erase.mp hz with ⟨hzn,hz⟩
  rcases Finset.mem_erase.mp hz with ⟨hzp,hz⟩
  exact ⟨z,hz,Ne.symm hzp,Ne.symm hzn⟩

theorem quadrant_signed_attachment (a : Network N m k) (S : Finset (Fin k)) (hS : 3≤S.card)
    (Q R : Fin m → ℝ) (q r : ℝ) (α β : Fin k → ℝ)
    (hrow : ∀ i∈S,∀ j,a.W₂ i j=α i*Q j+β i*R j)
    (hbias : ∀ i∈S,a.b₂ i=α i*q+β i*r)
    (hQ : ∀ x,0≤preact a.W₁ a.b₁ Q q x) (hR : ∀ x,0≤preact a.W₁ a.b₁ R r x)
    (hfit : ∀ u v : ℝ,0≤u → 0≤v → (∑ i in S,a.w₃ i*max 0 (α i*u+β i*v))=u-v)
    (ha : ∀ x,a.eval x=Maximum N x) :
    ∃ p n : Fin k,p∈S ∧ n∈S ∧ p≠n ∧
      JoinedIn (ExactSet N m k) a (signedNet a S p n (fun j=>Q j-R j) (q-r)) := by
  rcases quadrant_literal_alternative a S Q R q r α β hrow hbias hQ hR hfit ha with hs|hs
  · exact hs
  · rcases hs with ⟨p,n,hp,hn,hpn,hj⟩
    obtain ⟨z,hz,hpz,hnz⟩ := exists_spare_selected S hS p n hp hn hpn
    have hk := splitNet_joinedIn_signedNet a S p n z hp hn hz hpn hpz hnz Q R q r hQ hR hj.target_mem
    exact ⟨p,z,hp,hz,hpz,hj.trans hk⟩

end MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment
