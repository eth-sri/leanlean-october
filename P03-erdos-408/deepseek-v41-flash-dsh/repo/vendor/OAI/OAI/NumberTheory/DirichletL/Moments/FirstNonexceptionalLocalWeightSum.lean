module

public import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalFixedWeightSum
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCountSource

@[expose] public section

namespace OAI

noncomputable section

open Filter

namespace SevenEighths.CenteredMomentFirstNonexceptionalLocalWeightSum
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve RayFourExpansion CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalFixedWeightSum CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicCount CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentCanonicalFirst CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentSupportedCorrelation CenteredMomentSecondRetainedAggregate CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentExceptionalAmplitudePair
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def localRadius (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):ℝ:=
  frequencyRadius (firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData)) Z ξ

end SevenEighths.CenteredMomentFirstNonexceptionalLocalWeightSum

end

end OAI
