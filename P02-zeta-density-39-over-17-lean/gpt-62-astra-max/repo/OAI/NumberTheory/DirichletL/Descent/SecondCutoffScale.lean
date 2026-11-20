module
public import OAI.NumberTheory.DirichletL.Descent.SecondCorrelatedCutoff
public import OAI.NumberTheory.DirichletL.Descent.PhysicalExponents

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

end
end SevenEighths.InverseMoment

end OAI
