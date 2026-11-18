module
public import OAI.NumberTheory.DirichletL.Reflection.Sector


@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase ShortDraftCRT
open scoped Classical BigOperators MatrixGroups
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

end
end SevenEighths.InverseReflectedPhase

end OAI
