module

public import OAI.NumberTheory.DirichletL.Moments.EligibleEnergy
public import OAI.NumberTheory.DirichletL.Moments.RadialEligibleEnergy
public import OAI.NumberTheory.DirichletL.Moments.InductionEnergy

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentBottomStage
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]

end SevenEighths.CenteredMomentBottomStage

end

end OAI
