module

public import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalPrefactor
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCount

@[expose] public section

namespace OAI

noncomputable section

open Filter

namespace SevenEighths.CenteredMomentFirstNonexceptionalWeightSum
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstPhysicalDyadicCount CenteredMomentFirstNonexceptionalPrefactor CenteredMomentOriginalCommonHarmonic CenteredMomentCommonRadialData CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate CenteredMomentActiveSource CenteredMomentSupportedCorrelation CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentExceptionalAmplitudePair CenteredMomentSectorLocalization CenteredMomentRankinRadical
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev Labels (s:Input ι)(R seed:Ideal O):=
  ActiveLabel (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)

end SevenEighths.CenteredMomentFirstNonexceptionalWeightSum

end

end OAI
