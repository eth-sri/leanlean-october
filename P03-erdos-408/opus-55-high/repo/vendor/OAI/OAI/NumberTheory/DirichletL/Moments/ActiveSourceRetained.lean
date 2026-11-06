module

public import OAI.NumberTheory.DirichletL.Moments.SourceRectangleEnergy
public import OAI.NumberTheory.DirichletL.Moments.ActiveAllocation

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentActiveSourceRetained
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end SevenEighths.CenteredMomentActiveSourceRetained

end

end OAI
