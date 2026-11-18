module
public import OAI.NumberTheory.DirichletL.Reflection.PuncturedMarks
public import OAI.NumberTheory.DirichletL.Reflection.MarkedLevel


@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
open scoped Classical BigOperators
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {α σ : Type*} [Fintype σ]

end
end SevenEighths.InverseReflectedPhase

end OAI
