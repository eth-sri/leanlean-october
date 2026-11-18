module
public import OAI.NumberTheory.DirichletL.Moments.PrimeSlotExternal
public import OAI.NumberTheory.DirichletL.Moments.SlotNormalization

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentActualLiveSlotRemoval
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile CenteredMomentPrimeSlot CenteredMomentPrimeSlotExternal CenteredMomentWholeSlotDeletion ConcretePrimeRowBridge HeckePrimeAnnular
local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

end SevenEighths.CenteredMomentActualLiveSlotRemoval

end

end OAI
