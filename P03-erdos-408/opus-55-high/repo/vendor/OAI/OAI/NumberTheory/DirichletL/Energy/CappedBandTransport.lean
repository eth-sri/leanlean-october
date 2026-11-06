module

public import OAI.NumberTheory.DirichletL.Energy.CappedWidthInduction

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentEnergyCappedBandTransport
local notation "O"=>HeckeFamily.O
variable {α:Type*}
variable (M:Ideal HeckeFamily.O)[NeZero M]
local instance : Finite (HeckeFamily.O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (HeckeFamily.O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyCappedBandTransport

end

end OAI
