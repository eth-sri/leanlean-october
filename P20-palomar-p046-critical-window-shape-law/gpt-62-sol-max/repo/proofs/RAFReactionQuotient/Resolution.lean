module

public import proofs.RAFReactionQuotient.CriticalLimit
public import proofs.RAFReactionQuotient.SourceParameters
public import proofs.RAFReactionQuotient.CatalogueBridge
public import proofs.RAFReactionQuotient.SurvivalPositive
public import proofs.OverlapCorrectedRAF.Asymptotic.GatewayConditionedBulk

@[expose] public section

set_option Elab.async false

namespace RAFReactionQuotient
open Classical Filter MeasureTheory unitInterval HordijkSteelThreshold RAF.Polymer
open OverlapCorrectedRAF.Source
open scoped ENNReal Topology

noncomputable def criticalOpenness (lambda : ℝ) (hlambda : 0 < lambda) : I :=
  ⟨1-Real.exp (-lambda), by
    constructor
    · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    · linarith [Real.exp_pos (-lambda)]⟩

/-- Probability of infinite ordinary reversible closure in the canonical
repository-channel iid field, with all six food molecules. -/
noncomputable def quotientTransitionLimit (lambda : ℝ) (hlambda : 0 < lambda) : ℝ :=
  (quotientSurvival (criticalOpenness lambda hlambda)).toReal

end RAFReactionQuotient
