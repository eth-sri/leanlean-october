module

public import OAI.NumberTheory.DirichletL.Moments.PrimeSlotBound

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentPrimeSlotUniform
local notation "O" => HeckeFamily.O
variable (M:Ideal HeckeFamily.O) [NeZero M]
local instance : Finite (HeckeFamily.O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (HeckeFamily.O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

end SevenEighths.CenteredMomentPrimeSlotUniform

end

end OAI
