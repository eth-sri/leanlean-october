module
public import OAI.NumberTheory.DirichletL.Descent.MarkBounds
public import OAI.NumberTheory.DirichletL.Descent.PoissonTails


@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open FirstPassCubeLabels SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

end
end SevenEighths.InverseMoment

end OAI
