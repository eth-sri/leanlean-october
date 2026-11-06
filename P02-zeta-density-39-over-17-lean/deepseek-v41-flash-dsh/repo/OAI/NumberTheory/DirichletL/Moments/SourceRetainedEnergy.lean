module
public import OAI.NumberTheory.DirichletL.Moments.SourceRectangleEnergy

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceRetainedEnergy
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentRowNorm CenteredMomentDivisorRetained CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end SevenEighths.CenteredMomentSourceRetainedEnergy

end

end OAI
