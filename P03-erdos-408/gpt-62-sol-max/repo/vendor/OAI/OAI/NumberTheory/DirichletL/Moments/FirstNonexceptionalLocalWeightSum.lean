module

public import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalWeightSum
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCountSource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentFirstNonexceptionalLocalWeightSum
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentCanonicalFirst CenteredMomentFirstSectors
open CenteredMomentActiveSource CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSupportedCorrelation CenteredMomentSecondRetainedAggregate
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentExceptionalAmplitudePair
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def localRadius (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):ℝ:=
  frequencyRadius (firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData)) Z ξ

end SevenEighths.CenteredMomentFirstNonexceptionalLocalWeightSum

end

end OAI
