module
public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCapacity
public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceInternal

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary HeckeDetectorRawFiber ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
