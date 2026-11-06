
import proofs.RAFReactionQuotient.Fibres
import proofs.HordijkSteelThreshold.TargetTrials




namespace RAFReactionQuotient
open RAF.Polymer OverlapCorrectedRAF.Source HordijkSteelThreshold

variable (n : ℕ)

theorem splitToOrdered_surjective  : Function.Surjective (@splitToOrdered n) := by
  intro q
  obtain ⟨r,hl,hr,_⟩ := source_append_split
    (moleculeWord q.val.1) (moleculeWord q.val.2)
    (by rw [moleculeWord_length]; exact Nat.succ_pos _)
    (by rw [moleculeWord_length]; exact Nat.succ_pos _)
    (by simpa [moleculeWord_length] using q.property)
  refine ⟨r, Subtype.ext (Prod.ext ?_ ?_)⟩
  · exact moleculeWord_injective hl
  · exact moleculeWord_injective hr

theorem splitToQuotient_surjective  : Function.Surjective (@splitToQuotient n) :=
  (canonical_surjective n).comp (splitToOrdered_surjective n)



end RAFReactionQuotient
