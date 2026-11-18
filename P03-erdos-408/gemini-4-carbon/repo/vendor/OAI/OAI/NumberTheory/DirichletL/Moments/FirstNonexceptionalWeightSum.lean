module

public import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalPrefactor
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCount

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstNonexceptionalWeightSum
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstPhysicalDyadicCount CenteredMomentFirstNonexceptionalPrefactor
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonRadialData
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentActiveSource CenteredMomentSupportedCorrelation CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentRankinRadical
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev Labels (s:Input ι)(R seed:Ideal O):=
  ActiveLabel (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)

end SevenEighths.CenteredMomentFirstNonexceptionalWeightSum

end

end OAI
