module

public import OAI.NumberTheory.DirichletL.Descent.SecondSharpPuncture

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)

end
end SevenEighths.InverseMoment

end OAI
