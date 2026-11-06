module
public import OAI.NumberTheory.DirichletL.Reflection.Partition

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
open ActualEisensteinCubic CubicEisenstein CompletedGauss ConcreteTraceCRT LocalReflectionBrackets FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}
noncomputable local instance splitPhaseFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

end
end SevenEighths.InverseReflectedPhase

end OAI
