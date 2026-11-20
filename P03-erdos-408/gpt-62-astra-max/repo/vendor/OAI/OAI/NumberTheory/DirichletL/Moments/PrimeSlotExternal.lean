module

public import OAI.NumberTheory.DirichletL.Moments.PrimeSlotShift
public import OAI.NumberTheory.DirichletL.Moments.PrimeSlotUniform

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentPrimeSlotExternal
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile HeckePrimeAnnular
open CenteredMomentPrimeSlot CenteredMomentPrimeSlotUniform CenteredMomentWholeSlotDeletion
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

end SevenEighths.CenteredMomentPrimeSlotExternal

end

end OAI
