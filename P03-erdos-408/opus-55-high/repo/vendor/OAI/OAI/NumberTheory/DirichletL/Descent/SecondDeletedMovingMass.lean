module

public import OAI.NumberTheory.DirichletL.Descent.SecondDeletedMovingEnergy
public import OAI.NumberTheory.DirichletL.Descent.SecondOriginalMass
public import OAI.NumberTheory.DirichletL.Descent.SecondBalancedSource

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical
noncomputable section
local instance inverseSecondDeletedMovingMassUnits : Fintype ActualEisensteinCubic.Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]

end
end SevenEighths.InverseMoment

end OAI
