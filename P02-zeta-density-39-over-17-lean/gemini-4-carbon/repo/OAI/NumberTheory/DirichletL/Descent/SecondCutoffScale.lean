module
public import OAI.NumberTheory.DirichletL.Descent.SecondCorrelatedCutoff
public import OAI.NumberTheory.DirichletL.Descent.PhysicalExponents


@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open scoped BigOperators Classical
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

end
end SevenEighths.InverseMoment

end OAI
