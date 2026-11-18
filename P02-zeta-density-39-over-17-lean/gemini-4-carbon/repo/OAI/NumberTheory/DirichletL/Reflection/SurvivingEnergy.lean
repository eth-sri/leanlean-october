module
public import OAI.NumberTheory.DirichletL.Reflection.FilteredMeasure


@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
open scoped Classical BigOperators ContDiff
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

end
end SevenEighths.InverseReflectedPhase

end OAI
