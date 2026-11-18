module
public import OAI.NumberTheory.DirichletL.Reflection.Cofactor

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open ActualEisensteinCubic CubicEisenstein CompletedGauss ConcreteTraceCRT LocalReflectionBrackets FiniteGaussPhase
open scoped BigOperators Classical
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}
noncomputable local instance splitPhaseFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

end
end SevenEighths.InverseReflectedPhase

end OAI
