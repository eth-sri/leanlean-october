module

public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedCapacityCommon
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceSupport

@[expose] public section

namespace OAI

noncomputable section

open Filter

namespace SevenEighths.CenteredMomentSecondInputCapacitySource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAmplificationChildInput CenteredMomentAllocatedChildCapacity CenteredMomentFirstAmplifiedCapacityCommon CenteredMomentSourceLiveColumn CenteredMomentSecondCapacitySourceShift CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget CenteredMomentFirstPhysicalSourceSupport CenteredMomentOriginalCommonHarmonic CenteredMomentCommonHeightEnvelope
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

def lowerFactor (N:ℕ)(slotLower plainLower:ℝ):ℝ:=
  (min 1 slotLower)^N*plainLower^2

lemma lowerFactor_pos (N:ℕ)(slotLower plainLower:ℝ)(hs:0<slotLower)(hp:0<plainLower):
    0<lowerFactor N slotLower plainLower:=by unfold lowerFactor;positivity

theorem actual_lower_support (N:ℕ)(slotLower plainLower:ℝ)(hs:0<slotLower)(hp:0<plainLower)
    (s:Input ι)(hc:Fintype.card ι≤N)(hlo:slotLower≤s.lower)
    (hW₁:∀x,s.W₁ x≠0→plainLower≤x)(hW₂:∀x,s.W₂ x≠0→plainLower≤x)
    (R seed I:Ideal O)(hne:coefficient s R seed I≠0):
    lowerFactor N slotLower plainLower*volume s≤(I.absNorm:ℝ):=by
  have hm:0≤min 1 slotLower:=(lt_min zero_lt_one hs).le
  have hprod:(min 1 slotLower)^N≤∏i,s.lo i:=by
    apply (pow_le_pow_of_le_one hm (min_le_left _ _) hc).trans
    have hh:=Finset.prod_le_prod₀ (s:=Finset.univ) (f:=fun _:ι=>min 1 slotLower)
      (g:=fun i=>s.lo i) (fun _ _=>hm)
      (fun i _=>(min_le_right _ _).trans (hlo.trans (s.lower_le i)))
    simpa only [Finset.prod_const,Finset.card_univ] using hh
  have hh:=original_column_lower s R seed I plainLower plainLower hp.le hp.le hW₁ hW₂ hne
  change (∏i,s.lo i)*plainLower*plainLower*volume s≤(I.absNorm:ℝ) at hh
  apply le_trans _ hh
  have hv:0≤volume s:=(volume_pos s).le
  unfold lowerFactor
  nlinarith [mul_le_mul_of_nonneg_right hprod (mul_nonneg (sq_nonneg plainLower) hv)]

end SevenEighths.CenteredMomentSecondInputCapacitySource

end

end OAI
