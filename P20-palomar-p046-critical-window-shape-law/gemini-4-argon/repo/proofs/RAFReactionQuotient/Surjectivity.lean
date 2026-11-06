module

public import proofs.RAFReactionQuotient.Fibres
public import proofs.HordijkSteelThreshold.TargetTrials

@[expose] public section

namespace RAFReactionQuotient
open Classical RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source HordijkSteelThreshold

theorem splitToOrdered_surjective (n : ℕ) : Function.Surjective (@splitToOrdered n) := fun q => by
  obtain ⟨r, hl, hr, _⟩ := source_append_split (moleculeWord q.1.1) (moleculeWord q.1.2)
    (by rw [moleculeWord_length]; exact Nat.succ_pos _)
    (by rw [moleculeWord_length]; exact Nat.succ_pos _)
    (by simpa only [moleculeWord_length] using q.2)
  exact ⟨r, Subtype.ext (Prod.ext (moleculeWord_injective hl) (moleculeWord_injective hr))⟩

theorem quotient_mark_pullback_OR {n : ℕ} (ω : RepositoryChannel n → Prop) (j : RepositoryChannel n) :
    (∃ r : Reaction n, splitToQuotient r = j ∧ ω (splitToQuotient r)) ↔ ω j :=
  ⟨by rintro ⟨_, rfl, hr⟩; exact hr, fun hj => by
    obtain ⟨r, hr⟩ := ((canonical_surjective n).comp (splitToOrdered_surjective n)) j
    exact ⟨r, hr, by rwa [show splitToQuotient r = j from hr]⟩⟩

end RAFReactionQuotient
