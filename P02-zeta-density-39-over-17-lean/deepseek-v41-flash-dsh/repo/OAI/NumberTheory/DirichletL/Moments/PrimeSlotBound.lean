module
public import OAI.NumberTheory.DirichletL.Moments.PrimeSlot
public import OAI.NumberTheory.DirichletL.Moments.PrimeHeight

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentPrimeSlotBound
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion CenteredMomentRayNonprincipal
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)

include hH

end SevenEighths.CenteredMomentPrimeSlotBound

end

end OAI
