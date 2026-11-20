module
public import OAI.NumberTheory.DirichletL.Descent.SecondSharpPuncture

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)

end
end SevenEighths.InverseMoment

end OAI
