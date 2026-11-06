module

public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedCapacityRadius
public import OAI.NumberTheory.DirichletL.Moments.SecondCapacitySourceShift
public import OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
public import OAI.NumberTheory.DirichletL.Energy.InputParentCapacity

@[expose] public section

namespace OAI

noncomputable section


namespace SevenEighths.CenteredMomentFirstAmplifiedCapacitySource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ActualEisensteinCubic CenteredMomentSourceLiveColumn CenteredMomentFirstAmplifiedCapacityRadius CenteredMomentSecondCapacitySourceShift CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentCommonRawScale CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget CenteredMomentAmplifiedRetainedRadius
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]

theorem frozen_reduction_log (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C)
    (Z:ℝ)(hZ:1<Z)(hne:frozenCoefficient B.val C R s.ν s.W s.P≠0):
    Real.logb Z (rawReduction B.val s.P)-Real.logb Z (C.absNorm:ℝ)≤
      -(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower) := by
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have ha:0<min 1 s.lower:=lt_min zero_lt_one s.lower_pos
  have hh:=(actual_reduction_norm B.val (alloc_ne s C B) C R (allocation_product s C B)
    s.ν s.W s.P s.P_pos s.lower s.upper s.lower_pos s.slot_support hne).1
  have hl:=Real.logb_le_logb_of_le hZ (mul_pos (pow_pos ha _) hr) hh
  rw [Real.logb_mul (pow_pos ha _).ne' hr.ne',Real.logb_pow] at hl
  nlinarith

theorem inherited_affine_parent (s:Input ι)(C _R:Ideal O)(B:actualAllocations s.pools C)
    (Z κ M:ℝ)(hZ:1<Z)(hκ:1/6≤κ)(hP:∀i,1≤s.P i)
    (hcap:CenteredMomentEnergyBands.length Z s.X₁+
      CenteredMomentEnergyBands.length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    Real.logb Z (volume s)+(6*κ-1)*
      (∑i:CenteredMomentCommonProfile.liveIndices B.val,Real.logb Z (s.P i))≤M := by
  have hp:=CenteredMomentEnergyInputParentCapacity.input_affine_capacity s Z κ M hZ hcap
  have hs:=CenteredMomentAllocatedChildCapacity.common_slot_logs_le s C B Z hZ hP
  have hh:=mul_le_mul_of_nonneg_left hs (by linarith:0≤6*κ-1)
  linarith

end SevenEighths.CenteredMomentFirstAmplifiedCapacitySource

end

end OAI
