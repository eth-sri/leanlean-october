module

public import OAI.NumberTheory.DirichletL.Moments.PrimeSlotExternal
public import OAI.NumberTheory.DirichletL.Moments.SlotNormalization

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentActualLiveSlotRemoval
local notation "O" => HeckeFamily.O
variable (M:Ideal HeckeFamily.O) [NeZero M]
local instance : Finite (HeckeFamily.O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (HeckeFamily.O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

end SevenEighths.CenteredMomentActualLiveSlotRemoval

end

end OAI
