module
public import OAI.NumberTheory.DirichletL.Reflection.UpperThreshold


@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open CompletedDyadic CompletedGauss ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve InverseKernelSourceUniform
open scoped Classical BigOperators
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}

end
end SevenEighths.InverseReflectedPhase

end OAI
