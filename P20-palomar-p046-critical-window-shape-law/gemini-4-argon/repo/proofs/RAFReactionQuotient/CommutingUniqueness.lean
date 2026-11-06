module

public import proofs.RAFReactionQuotient.QuotientMap

@[expose] public section

namespace RAFReactionQuotient
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

theorem noncanonical_strict_lengths {n : ℕ} (r : OrderedChannel n)
    (h : ¬ (displayedConcat r.val.1 r.val.2 ≠ displayedConcat r.val.2 r.val.1 ∨
      moleculePrecedes r.val.1 r.val.2)) : molLength r.val.2 < molLength r.val.1 := by
  have hc : displayedConcat r.val.1 r.val.2 = displayedConcat r.val.2 r.val.1 :=
    Classical.byContradiction fun hn => h (Or.inl hn)
  have hn : ¬ moleculePrecedes r.val.1 r.val.2 := fun hp => h (Or.inr hp)
  have he : molLength r.val.1 ≠ molLength r.val.2 := fun he => hn <| Or.inr ⟨he, by
    have : 1 < 2 ^ molLength r.val.2 := Nat.one_lt_two_pow (Nat.succ_ne_zero _)
    unfold displayedConcat at hc
    rw [he] at hc
    nlinarith⟩
  unfold moleculePrecedes at hn
  omega

end RAFReactionQuotient
