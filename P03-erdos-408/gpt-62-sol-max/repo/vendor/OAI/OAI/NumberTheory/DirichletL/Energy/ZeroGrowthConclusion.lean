module

public import OAI.NumberTheory.DirichletL.Energy.ZeroGrowth
public import OAI.NumberTheory.DirichletL.Energy.ZeroGrowthReserve
public import OAI.NumberTheory.DirichletL.Energy.ZeroGrowthOriginal

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthConclusion
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyZeroGrowth CenteredMomentFiniteProfileExceptional
open CenteredMomentInductionEnergy QuadraticInitialBound
local notation "O" => HeckeFamily.O

end SevenEighths.CenteredMomentEnergyZeroGrowthConclusion

end

end OAI
