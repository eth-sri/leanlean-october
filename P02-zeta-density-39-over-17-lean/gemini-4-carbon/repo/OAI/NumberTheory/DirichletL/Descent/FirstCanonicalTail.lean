module
public import OAI.NumberTheory.DirichletL.Descent.FirstMarkedColumns


@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

end
end SevenEighths.InverseMoment

end OAI
