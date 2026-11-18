module
public import OAI.NumberTheory.DirichletL.Reflection.KernelActual


@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open CompletedDyadic ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
open scoped Classical BigOperators
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

end
end SevenEighths.InverseReflectedPhase

end OAI
