module

public import OAI.NumberTheory.DirichletL.Energy.ReferenceRobustPower

@[expose] public section

namespace OAI

noncomputable section



namespace SevenEighths.CenteredMomentEnergyReferenceLivePower

local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyReferenceLivePower

end

end OAI
