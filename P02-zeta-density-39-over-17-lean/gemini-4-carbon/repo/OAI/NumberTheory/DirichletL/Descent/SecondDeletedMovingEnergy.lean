module
public import OAI.NumberTheory.DirichletL.Descent.SecondDeletedPhysicalRecursive
public import OAI.NumberTheory.DirichletL.Descent.SecondBalancedSource

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic JointLogSeparation MeasureTheory SchwartzMap InverseInitialClippedColumns
open scoped BigOperators Classical ContDiff
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedMovingPhysicalUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
open InverseSecondProfileUniform InverseAmbientProfileTower
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

end
end SevenEighths.InverseMoment

end OAI
