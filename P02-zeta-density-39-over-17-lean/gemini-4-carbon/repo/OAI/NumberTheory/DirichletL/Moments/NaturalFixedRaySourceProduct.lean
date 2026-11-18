module
public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceSlots
public import OAI.NumberTheory.DirichletL.Moments.SlotNormalization

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckePrimeAnnular ConcretePrimeRowBridge CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily CenteredMomentHeckeHeight CenteredMomentHeckeTwist CenteredMomentRetainedEnergy CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot CenteredMomentSlotNormalization
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
