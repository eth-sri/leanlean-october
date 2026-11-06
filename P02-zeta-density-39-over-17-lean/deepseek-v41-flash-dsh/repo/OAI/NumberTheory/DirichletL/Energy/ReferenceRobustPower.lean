module
public import OAI.NumberTheory.DirichletL.Energy.ReferenceRobustOriginal
public import OAI.NumberTheory.DirichletL.Energy.ReferenceScalarReserve
public import OAI.NumberTheory.DirichletL.Energy.ReferenceProfileBudget

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceRobustPower
open HeckeFamily HeckeDyadic ConcreteTraceCRT CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceRobustOriginal CenteredMomentEnergyReferenceScalarReserve CenteredMomentEnergyReferenceProfileBudget CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyReferenceRobustPower

end

end OAI
