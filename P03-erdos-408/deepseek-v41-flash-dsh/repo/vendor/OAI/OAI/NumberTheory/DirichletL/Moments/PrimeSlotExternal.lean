module

public import OAI.NumberTheory.DirichletL.Moments.PrimeSlotShift
public import OAI.NumberTheory.DirichletL.Moments.PrimeSlotUniform

@[expose] public section

namespace OAI

noncomputable section


namespace SevenEighths.CenteredMomentPrimeSlotExternal

local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M]
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

end SevenEighths.CenteredMomentPrimeSlotExternal

end

end OAI
