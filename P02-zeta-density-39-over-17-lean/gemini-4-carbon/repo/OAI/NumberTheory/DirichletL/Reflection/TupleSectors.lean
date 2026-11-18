module
public import OAI.NumberTheory.DirichletL.Reflection.TupleFamily
public import OAI.NumberTheory.DirichletL.Reflection.SourceSectors


@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
open scoped Classical BigOperators
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ]

end
end SevenEighths.InverseReflectedPhase

end OAI
