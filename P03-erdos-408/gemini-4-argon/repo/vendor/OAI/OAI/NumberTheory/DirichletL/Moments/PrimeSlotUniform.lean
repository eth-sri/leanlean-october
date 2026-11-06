module

public import OAI.NumberTheory.DirichletL.Moments.PrimeSlotBound

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentPrimeSlotUniform
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentPrimeSlot CenteredMomentPrimeSlotBound CenteredMomentWholeSlotDeletion
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

end SevenEighths.CenteredMomentPrimeSlotUniform

end

end OAI
