module

public import proofs.HordijkSteelThreshold.PeelingHistory

@[expose] public section

namespace HordijkSteelThreshold
open Classical

theorem peelingActiveAt_fixed_persists {X R : Type*} [Fintype X]
    (response : Finset X → Finset R) (closure : Finset R → Finset X)
    {t : ℕ} (ht : peelingActiveAt response closure (t+1) = peelingActiveAt response closure t) :
    ∀ j, peelingActiveAt response closure (t+j) = peelingActiveAt response closure t
  | 0 => rfl
  | j + 1 => by rw [Nat.add_succ, peelingActiveAt, peelingActiveAt_fixed_persists _ _ ht j]; exact ht

theorem peelingActiveAt_stable_card {X R : Type*} [Fintype X] [Fintype R]
    (response : Finset X → Finset R) (closure : Finset R → Finset X)
    (hr : Monotone response) (hc : Monotone closure) :
    peelingActiveAt response closure (Fintype.card R+1) =
      peelingActiveAt response closure (Fintype.card R) := by
  have hanti := peelingActiveAt_antitone response closure hr hc
  by_contra hfail
  have hbound (t : ℕ) (ht : t ≤ Fintype.card R + 1) :
      (peelingActiveAt response closure t).card + t ≤ Fintype.card R := by
    induction t with
    | zero => simpa using Finset.card_le_univ _
    | succ t ih =>
      have hne : peelingActiveAt response closure (t + 1) ≠ peelingActiveAt response closure t := fun he => by
        have h1 := peelingActiveAt_fixed_persists response closure he (Fintype.card R + 1 - t)
        have h0 := peelingActiveAt_fixed_persists response closure he (Fintype.card R - t)
        rw [Nat.add_sub_of_le (by omega)] at h1
        rw [Nat.add_sub_of_le (by omega)] at h0
        exact hfail (h1.trans h0.symm)
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hanti (by omega : t ≤ t + 1), hne⟩)
      have := ih (by omega); omega
  have := hbound (Fintype.card R + 1) le_rfl; omega

end HordijkSteelThreshold
