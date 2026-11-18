module
public import OAI.NumberTheory.DirichletL.Moments.EligibleEnergy
public import OAI.NumberTheory.DirichletL.Moments.RadialEligibleEnergy
public import OAI.NumberTheory.DirichletL.Moments.InductionEnergy


@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentBottomStage
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy CenteredMomentInductionEnergy CenteredMomentAbsoluteEnergy QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]

end SevenEighths.CenteredMomentBottomStage

end

end OAI
