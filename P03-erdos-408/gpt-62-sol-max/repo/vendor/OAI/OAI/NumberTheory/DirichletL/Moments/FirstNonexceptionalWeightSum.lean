module

public import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalPrefactor
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCount

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open Filter

namespace SevenEighths.CenteredMomentFirstNonexceptionalWeightSum
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentFirstNonexceptionalPrefactor CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonRadialData CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentActiveSource CenteredMomentSupportedCorrelation
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentExceptionalAmplitudePair CenteredMomentSectorLocalization CenteredMomentRankinRadical
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev Labels (s:Input ι)(R seed:Ideal O):=
  ActiveLabel (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)

end SevenEighths.CenteredMomentFirstNonexceptionalWeightSum

end

end OAI
