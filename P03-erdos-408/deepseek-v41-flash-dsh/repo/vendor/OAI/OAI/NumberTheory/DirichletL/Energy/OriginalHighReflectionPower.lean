module

public import OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionOriginal
public import OAI.NumberTheory.DirichletL.Energy.ReferenceScalarReserve
public import OAI.NumberTheory.DirichletL.Energy.ReferenceProfileBudget

@[expose] public section

namespace OAI

noncomputable section



namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionPower

local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionPower

end

end OAI
