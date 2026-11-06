module

public import proofs.RAFReactionQuotient.Terminal
public import proofs.HordijkSteelThreshold.FixedPoolReactionLaw
public import proofs.RAFReactionQuotient.FiniteApproximation
public import proofs.HordijkSteelThreshold.SourceTerminalRAF
public import proofs.HordijkSteelThreshold.NearFullPoolAsymptotics
public import proofs.OverlapCorrectedRAF.Source.ActualGatewayDock

@[expose] public section

set_option Elab.async false

namespace RAFReactionQuotient
open Classical Filter MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal Topology

variable (n : ℕ)

def quotientRAFEvent  : Set (RepositoryChannel n → Molecule n → Prop) :=
  {ω | ∃ S, IsRevRAF (repositoryCRS n 2) (fun x j => ω j x) S}

noncomputable def quotientRAFProbability  (p : I) : ENNReal :=
  quotientCatalyticLaw n p $ quotientRAFEvent n

end RAFReactionQuotient
