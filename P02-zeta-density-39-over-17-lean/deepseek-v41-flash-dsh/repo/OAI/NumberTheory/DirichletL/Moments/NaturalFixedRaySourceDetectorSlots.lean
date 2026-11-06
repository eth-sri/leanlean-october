module
public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceDetectorCancellation

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeRowClosure ConcretePrimeRowBridge CenteredMomentDetectorDictionary CenteredMomentHeckeSlots CenteredMomentHeckeHeight CenteredExceptionalProfile CenteredMomentHeckeVolume
local notation "O" => HeckeFamily.O

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
