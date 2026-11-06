module

public import OAI.NumberTheory.DirichletL.Energy.ReferenceRobustOriginal
public import OAI.NumberTheory.DirichletL.Energy.ReferenceScalarReserve
public import OAI.NumberTheory.DirichletL.Energy.ReferenceProfileBudget

@[expose] public section

namespace OAI

noncomputable section



namespace SevenEighths.CenteredMomentEnergyReferenceRobustPower

local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyReferenceRobustPower

end

end OAI
