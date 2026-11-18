module
public import OAI.NumberTheory.DirichletL.Descent.FirstModeAssembly
public import OAI.NumberTheory.DirichletL.Descent.FirstModeChild


@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open MeasureTheory JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
open FirstCauchyArithmetic (supportIdealFamily supportIdealFamily_pos supportIdealFamily_good recoveredSupport supportRay)
open RayFourExpansion (RayCharacter)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
local notation "lambda" => ConcretePrimeRowBridge.goodLambda

end
end SevenEighths.InverseMoment

end OAI
