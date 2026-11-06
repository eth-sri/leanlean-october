module

public import OAI.NumberTheory.DirichletL.Moments.PrimeSlotExternal
public import OAI.NumberTheory.DirichletL.Moments.SlotNormalization

@[expose] public section

namespace OAI

noncomputable section


namespace SevenEighths.CenteredMomentActualLiveSlotRemoval

local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M]
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

end SevenEighths.CenteredMomentActualLiveSlotRemoval

end

end OAI
