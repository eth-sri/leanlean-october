module
public import OAI.NumberTheory.DirichletL.Reflection.ExtractedEnergy


@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
open scoped Classical BigOperators
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

end
end SevenEighths.InverseReflectedPhase

end OAI
