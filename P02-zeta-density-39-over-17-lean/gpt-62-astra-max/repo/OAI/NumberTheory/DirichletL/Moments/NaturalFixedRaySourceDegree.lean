module
public import OAI.NumberTheory.DirichletL.Moments.HeckeSlots

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeVolume
open CenteredMomentHeckeCancellation CenteredMomentHeckeTwist CenteredMomentLattice
open CenteredMomentMask CenteredMomentTwist CenteredMomentHeight CenteredMomentHeckeSlots
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
