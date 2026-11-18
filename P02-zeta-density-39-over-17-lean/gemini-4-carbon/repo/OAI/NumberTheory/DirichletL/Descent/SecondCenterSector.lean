module
public import OAI.NumberTheory.DirichletL.Descent.SecondVariableCutoff


@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open scoped BigOperators Classical
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι γ δ κ : Type*} [DecidableEq ι] [DecidableEq γ] [DecidableEq δ] [DecidableEq κ]

end
end SevenEighths.InverseMoment

end OAI
