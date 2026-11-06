module
public import OAI.NumberTheory.DirichletL.Inversion.SecondChildWindows

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff SchwartzMap

namespace SevenEighths.InverseMoment
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic JointLogSeparation MeasureTheory InverseInitialClippedColumns InverseSecondProfileUniform InverseAmbientProfileTower
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]

end SevenEighths.InverseMoment

end

end OAI
