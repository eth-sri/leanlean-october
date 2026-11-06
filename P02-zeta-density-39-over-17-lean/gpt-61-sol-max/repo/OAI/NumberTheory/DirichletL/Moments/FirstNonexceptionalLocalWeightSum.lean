module
public import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalWeightSum
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCountSource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstNonexceptionalLocalWeightSum
open ActualEisensteinCubic
open CenteredMomentFirstNonexceptionalWeightSum

open CenteredMomentCommonRadialData
open CenteredMomentCanonicalFirst


open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentExceptionalAmplitudePair
open scoped EisensteinO
variable {ι:Type*}[Fintype ι][DecidableEq ι]

local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def localRadius (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):ℝ:=
  frequencyRadius (firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData)) Z ξ






