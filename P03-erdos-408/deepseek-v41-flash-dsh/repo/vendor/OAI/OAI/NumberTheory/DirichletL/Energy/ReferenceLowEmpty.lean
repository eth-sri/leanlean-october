module

public import OAI.NumberTheory.DirichletL.Energy.ReferenceLowBands

@[expose] public section

namespace OAI

noncomputable section


namespace SevenEighths.CenteredMomentEnergyReferenceLowEmpty

local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α][IsEmpty α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyReferenceLowEmpty

end

end OAI
