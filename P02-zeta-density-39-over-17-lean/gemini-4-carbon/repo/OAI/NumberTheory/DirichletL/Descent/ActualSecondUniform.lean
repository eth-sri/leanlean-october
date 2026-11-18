module
public import OAI.NumberTheory.DirichletL.Descent.ActualSecondMeasure

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v w

end
end SevenEighths.InverseMoment

end OAI
