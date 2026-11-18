module
public import OAI.NumberTheory.DirichletL.Reflection.SumEnergy


@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open MeasureTheory ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
open scoped Classical BigOperators
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {Ω φ σ : Type*} [MeasurableSpace Ω] [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}

end
end SevenEighths.InverseReflectedPhase

end OAI
