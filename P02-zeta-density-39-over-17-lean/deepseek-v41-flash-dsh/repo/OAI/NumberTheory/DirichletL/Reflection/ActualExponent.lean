module
public import OAI.NumberTheory.DirichletL.Reflection.UpperThreshold

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic CompletedGauss ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve InverseKernelSourceUniform
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}

end
end SevenEighths.InverseReflectedPhase

end OAI
