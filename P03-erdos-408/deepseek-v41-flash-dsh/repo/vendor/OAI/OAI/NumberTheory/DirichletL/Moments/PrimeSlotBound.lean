module

public import OAI.NumberTheory.DirichletL.Moments.PrimeSlot
public import OAI.NumberTheory.DirichletL.Moments.PrimeHeight

@[expose] public section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentPrimeSlotBound

local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M]
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)

include hH

end SevenEighths.CenteredMomentPrimeSlotBound

end

end OAI
