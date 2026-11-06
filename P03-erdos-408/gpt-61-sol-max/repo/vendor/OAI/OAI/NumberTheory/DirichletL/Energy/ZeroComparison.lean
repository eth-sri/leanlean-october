module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Energy.OriginalSource
public import OAI.NumberTheory.DirichletL.Moments.RetainedProfile

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroComparison
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEnergyOriginalSource
open CenteredMomentRadialEligibleEnergy CenteredMomentInductionEnergy
open CenteredMomentRetainedProfile CenteredMomentRetainedEnergy
open CenteredMomentHeckeExpansion CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentSourceRow
open CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceProfileMass CenteredMomentHeckeHeight CenteredMomentSourceMass

variable {ι:Type*}[Fintype ι][DecidableEq ι]


def smallScale (b:ℝ):=1/(2*max 1 b)

lemma smallScale_pos  b :0<smallScale b:=by unfold smallScale;positivity

lemma smallScale_le_one  b :smallScale b≤1:=by
  unfold smallScale
  bound

lemma smallScale_strict  b :smallScale b*b<1:=by
  have hm:0<max 1 b:=zero_lt_one.trans_le (le_max_left _ _)
  unfold smallScale
  have hb:=le_max_right (1:ℝ) b
  rw [div_mul_eq_mul_div,one_mul]
  exact (div_lt_iff₀ (mul_pos (by norm_num) hm)).mpr (by linarith)

def zeroData (s:Input ι) := { s.toData with
  Y₁ := smallScale s.b₁
  Y₂ := s.X₁*s.X₂/smallScale s.b₁
  Y₁_pos := smallScale_pos _
  Y₂_pos := div_pos (mul_pos s.X₁_pos s.X₂_pos) (smallScale_pos _)
  same_product := by field_simp [ne_of_gt (smallScale_pos s.b₁)] }

def zeroInput (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0) :=
  completeInput (zeroData s) hz₁ hz₂ s.ν_bound s.W_bound s.lower s.upper
    s.lower_pos s.lower_le s.upper_ge

omit [DecidableEq ι] in
@[simp] lemma zeroInput_volume (s:Input ι) hz₁  hz₂ :
    volume (zeroInput s hz₁ hz₂)=volume s:=rfl

omit [DecidableEq ι] in
lemma comparison_row_zero (s:Input ι) hz₁  hz₂ 
     R  z :
    positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂=0:=by
  unfold positiveSlotRow
  change _*(rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.t (smallScale s.b₁)*_*_)=0
  rw [strict_subunit_rowTwistedSum_zero s.η (fixedBadMask*idealGenerator R) 1 z
    s.W₁ s.b₁ s.t (smallScale s.b₁) (smallScale_pos _) s.support₁ (smallScale_strict _)]
  simp only [zero_mul,mul_zero]

omit [DecidableEq ι] in
lemma comparison_energy_zero (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (R:Ideal HeckeFamily.O)(r:Radial):
    CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂
      r.keep r.profile r.scale=0:=by
  simp_all [CenteredMomentInductionEnergy.energy, comparison_row_zero]

end SevenEighths.CenteredMomentEnergyZeroComparison

end

end OAI
