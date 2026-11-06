module

public import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalFixedWeightSum
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCountSource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstNonexceptionalLocalWeightSum
open ActualEisensteinCubic HeckeFamily
open CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentCommonRadialData
open CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentExceptionalAmplitudePair
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def localRadius (s:Input ι)(R seed:Ideal ActualEisensteinCubic.O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):ℝ:=
  frequencyRadius (firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData)) Z ξ

end SevenEighths.CenteredMomentFirstNonexceptionalLocalWeightSum

end

end OAI
