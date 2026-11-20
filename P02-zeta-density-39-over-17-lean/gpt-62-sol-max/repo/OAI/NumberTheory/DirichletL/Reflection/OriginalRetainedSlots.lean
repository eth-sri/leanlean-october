module
public import OAI.NumberTheory.DirichletL.Reflection.PuncturedMarks
public import OAI.NumberTheory.DirichletL.Reflection.MarkedLevel

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {α σ : Type*} [Fintype σ]

end
end SevenEighths.InverseReflectedPhase

end OAI
