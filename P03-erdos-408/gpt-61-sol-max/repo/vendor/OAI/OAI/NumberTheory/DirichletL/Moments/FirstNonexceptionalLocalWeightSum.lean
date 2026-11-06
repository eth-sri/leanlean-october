module

public import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalFixedWeightSum
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCountSource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstNonexceptionalLocalWeightSum
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalFixedWeightSum
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSupportedCorrelation CenteredMomentSecondRetainedAggregate
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentExceptionalAmplitudePair

variable {ι:Type*}[Fintype ι][DecidableEq ι]


def localRadius (s:Input ι)(R seed)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):=
  frequencyRadius (firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData)) Z ξ

end SevenEighths.CenteredMomentFirstNonexceptionalLocalWeightSum

end

end OAI
