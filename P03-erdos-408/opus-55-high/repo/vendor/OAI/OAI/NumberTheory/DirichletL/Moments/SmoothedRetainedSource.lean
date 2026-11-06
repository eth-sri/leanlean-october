module

public import OAI.NumberTheory.DirichletL.Moments.SourceRetainedEnergy
public import OAI.NumberTheory.DirichletL.Moments.PositiveSummability

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentSmoothedRetainedSource
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

end SevenEighths.CenteredMomentSmoothedRetainedSource

end

end OAI
