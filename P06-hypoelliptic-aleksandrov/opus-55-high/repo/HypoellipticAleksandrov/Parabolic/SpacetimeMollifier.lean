module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Spacetime mollifiers

This module fixes a volume-normalized smooth mollifier on time--velocity
space and its left-kernel convolution orientation.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set
open scoped Convolution Pointwise Topology

namespace HypoellipticAleksandrov.Parabolic.SpacetimeMollifier

local instance timeVelocityVolumeIsAddHaarMeasure (d : ℕ) :
    Measure.IsAddHaarMeasure (volume : Measure (TimeVelocity d)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- The volume-normalized smooth spacetime mollifier at a real scale. -/
def spacetimeMollifier
    {d : ℕ} (ε : ℝ) (z : TimeVelocity d) : ℝ :=
  (((∫ x : TimeVelocity d,
      ExistsContDiffBumpBase.u x
      ∂(volume : Measure (TimeVelocity d))) *
      |ε| ^ Module.finrank ℝ (TimeVelocity d))⁻¹) *
    ExistsContDiffBumpBase.u (ε⁻¹ • z)

/-- Convolution with the common spacetime mollifier, kernel on the left. -/
def spacetimeMollification
    {d : ℕ} (ε : ℝ) (f : TimeVelocity d → ℝ) :
    TimeVelocity d → ℝ :=
  spacetimeMollifier ε ⋆[
    ContinuousLinearMap.lsmul ℝ ℝ,
    (volume : Measure (TimeVelocity d))] f

private theorem bump_volume_integral_pos (d : ℕ) :
    0 < ∫ x : TimeVelocity d, ExistsContDiffBumpBase.u x
      ∂(volume : Measure (TimeVelocity d)) := by
  refine (integral_pos_iff_support_of_nonneg ExistsContDiffBumpBase.u_nonneg ?_).mpr ?_
  · exact (ExistsContDiffBumpBase.u_smooth _).continuous
      |>.integrable_of_hasCompactSupport
        (ExistsContDiffBumpBase.u_compact_support _)
  · rw [ExistsContDiffBumpBase.u_support]
    exact Metric.measure_ball_pos _ 0 zero_lt_one

variable {d : ℕ} {ε : ℝ}

/-- The spacetime mollifier is nonnegative at every real scale. -/
theorem spacetimeMollifier_nonneg
     (ε : ℝ) (z : TimeVelocity d) :
    0 ≤ spacetimeMollifier ε z := mul_nonneg
    (inv_nonneg.mpr (mul_nonneg (bump_volume_integral_pos d).le
      (pow_nonneg (abs_nonneg ε) _)))
    (ExistsContDiffBumpBase.u_nonneg _)

/-- A positive-radius spacetime mollifier has literal volume integral one. -/
theorem spacetimeMollifier_integral
     (hε : 0 < ε) :
    (∫ z : TimeVelocity d,
      spacetimeMollifier ε z
      ∂(volume : Measure (TimeVelocity d))) = 1 := by
  simp_rw [spacetimeMollifier, ← smul_eq_mul, integral_smul]
  rw [Measure.integral_comp_inv_smul_of_nonneg
    volume
    (ExistsContDiffBumpBase.u : TimeVelocity d → ℝ) hε.le,
    abs_of_nonneg hε.le]
  simp only [smul_eq_mul]
  have hden :
      (∫ x : TimeVelocity d, ExistsContDiffBumpBase.u x ∂volume) *
          ε ^ Module.finrank ℝ (TimeVelocity d) ≠ 0 :=
    mul_ne_zero (bump_volume_integral_pos d).ne' (pow_ne_zero _ hε.ne')
  grind

/-- The function support of a positive-radius mollifier is the exact open
ball of that radius. -/
theorem spacetimeMollifier_support
     (hε : 0 < ε) :
    Function.support (spacetimeMollifier (d := d) ε) =
      Metric.ball 0 ε := by
  have hball : ε • Metric.ball (0 : TimeVelocity d) 1 = Metric.ball 0 ε := by
    rw [smul_unitBall hε.ne', Real.norm_of_nonneg hε.le]
  have hpow : ε ^ Module.finrank ℝ (TimeVelocity d) ≠ 0 :=
    pow_ne_zero _ hε.ne'
  have hnormal :
      ((∫ x : TimeVelocity d, ExistsContDiffBumpBase.u x ∂volume) *
        |ε| ^ Module.finrank ℝ (TimeVelocity d))⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (bump_volume_integral_pos d).ne' (by
      positivity))
  change Function.support (fun z : TimeVelocity d =>
      (((∫ x : TimeVelocity d, ExistsContDiffBumpBase.u x ∂volume) *
        |ε| ^ Module.finrank ℝ _)⁻¹) *
          ExistsContDiffBumpBase.u (ε⁻¹ • z)) = Metric.ball 0 ε
  rw [support_mul, support_const hnormal, univ_inter,
    support_comp_inv_smul₀ hε.ne', ExistsContDiffBumpBase.u_support, hball]

/-- The topological support of a positive-radius mollifier is the exact closed
ball of that radius. -/
theorem spacetimeMollifier_tsupport
     (hε : 0 < ε) :
    tsupport (spacetimeMollifier (d := d) ε) =
      Metric.closedBall 0 ε := by
  rw [tsupport, spacetimeMollifier_support hε, closure_ball _ hε.ne']

/-- A positive-radius spacetime mollifier has compact support. -/
theorem spacetimeMollifier_hasCompactSupport
     (hε : 0 < ε) :
    HasCompactSupport (spacetimeMollifier (d := d) ε) := by
  rw [HasCompactSupport, spacetimeMollifier_tsupport hε]
  exact isCompact_closedBall _ _

/-- A spacetime mollifier is smooth at every real scale. -/
theorem spacetimeMollifier_contDiff
     (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (spacetimeMollifier (d := d) ε) := contDiff_const.mul
    ((ExistsContDiffBumpBase.u_smooth _).comp
      (contDiff_id.const_smul _))

/-- The spacetime mollifier is even. -/
theorem spacetimeMollifier_neg
     (ε : ℝ) (z : TimeVelocity d) :
    spacetimeMollifier ε (-z) = spacetimeMollifier ε z := by
  unfold spacetimeMollifier
  rw [smul_neg, ExistsContDiffBumpBase.u_neg]

/-- Convolution with a positive-radius spacetime mollifier is smooth when the
raw function is locally integrable. -/
theorem contDiff_spacetimeMollification
     (hε : 0 < ε)
    (f : TimeVelocity d → ℝ)
    (hf : LocallyIntegrable f
      (volume : Measure (TimeVelocity d))) :
    ContDiff ℝ (⊤ : ℕ∞) (spacetimeMollification ε f) := (spacetimeMollifier_hasCompactSupport hε).contDiff_convolution_left
    _ (spacetimeMollifier_contDiff ε) hf

end HypoellipticAleksandrov.Parabolic.SpacetimeMollifier
