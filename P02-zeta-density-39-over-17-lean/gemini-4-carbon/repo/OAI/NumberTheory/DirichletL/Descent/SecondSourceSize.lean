module
public import OAI.NumberTheory.DirichletL.Descent.FirstSourceSize
public import OAI.NumberTheory.DirichletL.Descent.SecondCanonicalTail


@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open scoped BigOperators Classical
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)

end
end SevenEighths.InverseMoment

end OAI
