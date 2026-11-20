module
public import OAI.NumberTheory.DirichletL.Descent.MarkBounds
public import OAI.NumberTheory.DirichletL.Descent.PoissonTails

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

end
end SevenEighths.InverseMoment

end OAI
