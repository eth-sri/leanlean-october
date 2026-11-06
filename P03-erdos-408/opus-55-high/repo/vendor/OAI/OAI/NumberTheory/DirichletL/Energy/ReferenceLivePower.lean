module

public import OAI.NumberTheory.DirichletL.Energy.ReferenceRobustPower

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentEnergyReferenceLivePower
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal HeckeFamily.O)[NeZero M]
local instance : Finite (HeckeFamily.O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (HeckeFamily.O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyReferenceLivePower

end

end OAI
