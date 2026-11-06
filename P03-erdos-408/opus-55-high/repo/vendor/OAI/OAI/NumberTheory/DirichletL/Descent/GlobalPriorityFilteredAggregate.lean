module

public import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityAggregate
public import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFilteredRays
public import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityPhysical

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.InverseMoment
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
end SevenEighths.InverseMoment

end

end OAI
