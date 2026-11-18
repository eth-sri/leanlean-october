module
public import OAI.NumberTheory.DirichletL.Reflection.Brackets

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets CanonicalQuadraticSieve
open scoped Classical BigOperators
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance branchFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

end
end SevenEighths.InverseReflectedPhase

end OAI
