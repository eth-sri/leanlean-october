module
public import OAI.NumberTheory.DirichletL.Descent.FirstModeAssembly
public import OAI.NumberTheory.DirichletL.Descent.FirstModeChild

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels
open FirstCauchyArithmetic (supportIdealFamily supportIdealFamily_pos supportIdealFamily_good recoveredSupport supportRay)
open RayFourExpansion (RayCharacter)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
local notation "lambda" => ConcretePrimeRowBridge.goodLambda

end
end SevenEighths.InverseMoment

end OAI
