module

public import proofs.RAFReactionQuotient.CriticalLimit
public import proofs.RAFReactionQuotient.SourceParameters
public import proofs.RAFReactionQuotient.CatalogueBridge
public import proofs.RAFReactionQuotient.SurvivalPositive
public import proofs.OverlapCorrectedRAF.Asymptotic.GatewayConditionedBulk

@[expose] public section

namespace RAFReactionQuotient
open unitInterval

noncomputable def criticalOpenness (lambda : ℝ) (hlambda : 0 < lambda) : I :=
  ⟨1-Real.exp (-lambda), by
    constructor
    · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    · linarith [Real.exp_pos (-lambda)]⟩

end RAFReactionQuotient
