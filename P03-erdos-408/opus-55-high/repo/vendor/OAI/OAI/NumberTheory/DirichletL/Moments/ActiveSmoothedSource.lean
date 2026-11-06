module

public import OAI.NumberTheory.DirichletL.Moments.ActiveSourceRetained
public import OAI.NumberTheory.DirichletL.Moments.PositiveSummability

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentActiveSmoothedSource
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

end SevenEighths.CenteredMomentActiveSmoothedSource

end

end OAI
