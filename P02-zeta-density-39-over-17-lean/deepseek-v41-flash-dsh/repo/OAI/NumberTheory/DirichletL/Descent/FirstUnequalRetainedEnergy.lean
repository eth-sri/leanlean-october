module
public import OAI.NumberTheory.DirichletL.Descent.FirstUnequalMovingEnergy
public import OAI.NumberTheory.DirichletL.Descent.FirstActualSecondEnergy

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
open InverseMomentFirstProfileUniform InverseAmbientProfileTower
variable {ι : Type*} [DecidableEq ι]

end
end SevenEighths.InverseMoment

end OAI
