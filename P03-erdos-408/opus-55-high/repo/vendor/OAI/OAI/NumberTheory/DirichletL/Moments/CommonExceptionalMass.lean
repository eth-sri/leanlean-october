module

public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalCost

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentCommonExceptionalMass
open CenteredMomentCommonLinearNormalization CenteredMomentCommonRadialData
open CenteredMomentCommonExceptionalCost CenteredMomentCommonAllocationSum
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentAllocatedDetectorAmplitude
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma scalar_profile_volume (s:Input ι)(C R:Ideal HeckeFamily.O)(hC:C≠0)(B:actualAllocations s.pools C):
    ‖commonScalar s C R B‖*slotControl (commonData s C R B)*Real.sqrt (volume (commonData s C R B))≤
      slotControl s.toData*frozenProfile s*Real.sqrt (volume s.toData)/(Ideal.absNorm C:ℝ):=by
  calc
    _=slotControl (commonData s C R B)*
        (‖commonScalar s C R B‖*Real.sqrt (volume (commonData s C R B))):=by ring
    _≤slotControl s.toData*(frozenProfile s*Real.sqrt (volume s.toData)/(Ideal.absNorm C:ℝ)):=
      mul_le_mul (common_slotControl s C R B) (scalar_volume_bound s C R hC B)
        (by positivity) (slotControl_nonneg s.toData)
    _=_:=by ring

end SevenEighths.CenteredMomentCommonExceptionalMass

end

end OAI
