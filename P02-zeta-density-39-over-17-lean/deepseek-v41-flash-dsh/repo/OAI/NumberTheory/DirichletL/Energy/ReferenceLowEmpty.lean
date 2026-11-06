module
public import OAI.NumberTheory.DirichletL.Energy.ReferenceLowBands

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowEmpty
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy CenteredMomentRetainedEnergy CenteredMomentFiniteProfileExceptional QuadraticInitialBound
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α][IsEmpty α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyReferenceLowEmpty

end

end OAI
