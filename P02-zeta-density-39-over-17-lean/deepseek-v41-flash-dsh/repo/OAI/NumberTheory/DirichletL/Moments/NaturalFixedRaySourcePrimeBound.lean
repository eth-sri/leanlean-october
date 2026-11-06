module
public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourcePrimeGate

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate ContDiff Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily HeckePrimeRay CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily ConcretePrimeRowBridge CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot HeckeZeroSupremum
local notation "O" => HeckeFamily.O
variable {Δ : ℝ} {D : Parameters.HighData Δ}

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
