module
public import OAI.NumberTheory.DirichletL.Reflection.KernelActual


@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
open scoped Classical BigOperators ContDiff
noncomputable section
universe u
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

end
end SevenEighths.InverseReflectedPhase

end OAI
