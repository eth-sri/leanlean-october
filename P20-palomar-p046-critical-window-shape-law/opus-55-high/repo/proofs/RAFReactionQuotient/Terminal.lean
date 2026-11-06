module

public import proofs.RAFReactionQuotient.FiniteApproximation
public import proofs.RAFEmergenceApprox.SourceEvent
public import proofs.RAFEmergenceApprox.ThresholdSweep
public import proofs.HordijkSteelThreshold.SourceTerminalRAF

@[expose] public section

set_option Elab.async false

namespace RAFReactionQuotient
open Classical RAF RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source HordijkSteelThreshold
open RAFEmergenceApprox.Generic

noncomputable def splitPreimage {n : ℕ} (A : Finset $ RepositoryChannel n) : Finset (Reaction n) :=
  Finset.univ.filter $ fun r => splitToQuotient r ∈ A

theorem quotientClosure_preimage {n L : ℕ} (A : Finset $ RepositoryChannel n) :
    quotientClosure n L A = temporaryReactionClosure L (splitPreimage A) := by
  convert quotientClosure_pullback (n := n) (L := L) (· ∈ A) <;> ext <;> simp [quotientOpen, splitPreimage, staticOpenReactions]

end RAFReactionQuotient
