module

public import OAI.NumberTheory.DirichletL.Moments.CommonRadialSource
public import OAI.NumberTheory.DirichletL.Moments.CommonRadialCost
public import OAI.NumberTheory.DirichletL.Moments.RadialPointwiseUniform

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentCommonRadialPointwise
open CenteredMomentCommonRadialData
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

 def profileCost (s:Input ι) : ℝ :=
  ((∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)*s.toData.profileFactor

omit [DecidableEq ι] in
lemma profileCost_nonneg (s:Input ι) : 0≤profileCost s :=
  mul_nonneg (by positivity) s.toData.profile_nonneg

end SevenEighths.CenteredMomentCommonRadialPointwise

end

end OAI
