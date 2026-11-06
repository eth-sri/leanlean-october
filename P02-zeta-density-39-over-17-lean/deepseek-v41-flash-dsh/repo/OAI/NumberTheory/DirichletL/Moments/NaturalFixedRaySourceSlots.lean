module
public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCharacters

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckePrimeRay HeckePrimeAnnular ConcretePrimeRowBridge CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot CenteredMomentDetectorDictionary
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
