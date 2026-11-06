module

public import OAI.NumberTheory.DirichletL.Moments.SourceRectangleEnergy
public import OAI.NumberTheory.DirichletL.Moments.ActiveAllocation

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentActiveSourceRetained
open CenteredMomentActiveAllocation HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end SevenEighths.CenteredMomentActiveSourceRetained

end

end OAI
