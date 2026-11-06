module
public import OAI.NumberTheory.DirichletL.Moments.CommonLinearSource
public import OAI.NumberTheory.DirichletL.Moments.CommonRawCost

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonLinearNormalization
open HeckeFamily CenteredMomentCommonLinearSource CenteredMomentCommonRadialData
open CenteredMomentCommonRawScale CenteredMomentCommonRawCost CenteredMomentEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalMaskedSource CenteredMomentExceptionalAmplitudePair
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def commonScalar (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):ℂ:=
  (Real.sqrt (rawReduction B.val s.P):ℂ)⁻¹*frozenCoefficient B.val C R s.ν s.W s.P

omit [DecidableEq ι] in
theorem common_volume (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):
    volume (commonData s C R B)=remainingRaw B.val (s.X₁*s.X₂) s.P:=by
  dsimp only [volume,commonData,remainingRaw,plainNorm]
  ring

theorem source_normalized (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (hseed:seed∣C)(z:O):
    (Real.sqrt (volume s.toData):ℂ)⁻¹*sourceColumn s C hC R seed L z=
      ∑B:actualAllocations s.pools C,commonScalar s C R B*maskedAmplitude (commonData s C R B) L z:=by
  rw [source_column_allocation s C hC R seed L hseed z,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  rw [live_column_rectangle]
  have hv:=volume_pos (commonData s C R B)
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have he:volume (commonData s C R B)*rawReduction B.val s.P=volume s.toData:=by
    rw [common_volume]
    exact raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P
  have hs:Real.sqrt (volume s.toData)=Real.sqrt (volume (commonData s C R B))*
      Real.sqrt (rawReduction B.val s.P):=by rw [←he,Real.sqrt_mul hv.le]
  unfold commonScalar maskedAmplitude
  change (Real.sqrt (volume s.toData):ℂ)⁻¹*(_*_) =
    ((Real.sqrt (rawReduction B.val s.P):ℂ)⁻¹*_)*
      ((Real.sqrt (volume (commonData s C R B)):ℂ)⁻¹*_)
  rw [hs,Complex.ofReal_mul,mul_inv_rev]
  ring

end SevenEighths.CenteredMomentCommonLinearNormalization

end

end OAI
