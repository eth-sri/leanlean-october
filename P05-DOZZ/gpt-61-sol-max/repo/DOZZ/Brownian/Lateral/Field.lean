/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.RadialProjection
public import DOZZ.GFFStructure.GaussianIntegration
public import DOZZ.GFFStructure.OffCenterDecomposition

/-!
# The origin lateral field on the whole punctured plane

Subtract the radial Bochner average from every smooth test supported away from the origin.
The resulting test family and all origin circles belong to the same closed Gaussian space.
The concentric covariance identifies the radial average as the orthogonal radial projection.
Consequently the entire real radial process is independent of the whole lateral test family.

No pointwise lateral noise is defined: lateral coordinates are evaluations of the distribution
against smooth compact tests. The covariance calculation applies to tests on either side of the
equator and to tests crossing it.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- Scalar concentric covariance written in plane coordinates. -/
noncomputable def originRadialCovariance (s : ℝ) (w : ℂ) : ℝ :=
  min s (-Real.log ‖w‖) + max 0 (-s) + max 0 (Real.log ‖w‖)

/-- The plane potential of one origin circle is precisely the radial covariance. -/
theorem origin_circleKernelPotential_eq (s : ℝ) (w : ℂ) (hw : w ≠ 0) :
    (∫ v, gffKernel w v ∂circleMeasure 0 s) = originRadialCovariance s w := by
  have hnorm  := norm_pos_iff.mpr hw
  rw [integral_gffKernel_circleMeasure, integral_log_normPlus_circleMeasure_origin_eq_max,
    zero_sub, norm_neg, neg_log_max_exp_eq_min hnorm]
  unfold originRadialCovariance
  have hpin : Real.log (normPlus w) = max 0 (Real.log ‖w‖) := by
    unfold normPlus
    rcases le_total 1 ‖w‖ with hn | hn
    · rw [max_eq_right hn, max_eq_right (Real.log_nonneg hn)]
    · rw [max_eq_left hn, Real.log_one,
        max_eq_left (Real.log_nonpos hnorm.le hn)]
  rw [hpin]
  ring

section

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The actual radial/circle covariance has the same scalar plane kernel. -/
theorem origin_circle_radial_covariance (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (s : ℝ) (w : ℂ) :
    covariance (fun ω => Xc ω 0 s)
      (fun ω => Xc ω 0 (-Real.log ‖w‖)) P = originRadialCovariance s w := by
  rw [circleAverage_covariance_integral P X Xc hX hc,
    integral_integral_gffKernel_origin]
  simp only [originRadialCovariance, neg_neg]

end

/-- The equator pin terms are the positive parts of the logarithmic radius. -/
theorem log_normPlus_eq_max_log {w : ℂ} (hw : w ≠ 0) :
    Real.log (normPlus w) = max 0 (Real.log ‖w‖) := by
  have hnorm  := norm_pos_iff.mpr hw
  unfold normPlus
  rcases le_total 1 ‖w‖ with hn | hn
  · rw [max_eq_right hn, max_eq_right (Real.log_nonneg hn)]
  · rw [max_eq_left hn, Real.log_one, max_eq_left (Real.log_nonpos hnorm.le hn)]

variable {w v : ℂ} (hw : w ≠ 0) (hv : v ≠ 0)

include w v hw hv in
/-- The radial covariance at two geometric radii, including radii outside the unit circle. -/
theorem originRadialCovariance_log_radius  :
    originRadialCovariance (-Real.log ‖w‖) v =
      -Real.log (max ‖w‖ ‖v‖) + Real.log (normPlus w) + Real.log (normPlus v) := by
  rw [originRadialCovariance, neg_neg,
    min_neg_log_eq_neg_log_max (norm_pos_iff.mpr hw) (norm_pos_iff.mpr hv),
    log_normPlus_eq_max_log hw, log_normPlus_eq_max_log hv]

include w v hw hv in
/-- Subtracting the radial covariance cancels the two equator pin terms pointwise. -/
theorem origin_lateralKernel_cancellation  :
    gffKernel w v - originRadialCovariance (-Real.log ‖w‖) v =
      -Real.log ‖w - v‖ + Real.log (max ‖w‖ ‖v‖) := by
  rw [originRadialCovariance_log_radius hw hv, gffKernel]
  ring

include w v hw hv in
/-- The lateral kernel is a logarithm of the scale-free separation. -/
theorem origin_lateralKernel_normalized  (hsep : w ≠ v) :
    gffKernel w v - originRadialCovariance (-Real.log ‖w‖) v =
      Real.log (max ‖w‖ ‖v‖ / ‖w - v‖) := by
  rw [origin_lateralKernel_cancellation hw hv,
    Real.log_div (ne_of_gt ((norm_pos_iff.mpr hw).trans_le (le_max_left _ _)))
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hsep))]
  ring

/-- The scale-free separation is unchanged by any nonzero common complex dilation. -/
theorem origin_lateral_normalized_separation_dilation
    (c w v : ℂ) (hc : c ≠ 0) :
    max ‖c * w‖ ‖c * v‖ / ‖c * w - c * v‖ = max ‖w‖ ‖v‖ / ‖w - v‖ := by
  rw [← mul_sub, norm_mul, norm_mul, norm_mul,
    ← mul_max_of_nonneg _ _ (norm_nonneg c)]
  field_simp

/-- Common plane dilation corresponds to real cylinder translation and rotation. The exact
lateral covariance is invariant, including across the equator. -/
theorem origin_lateralKernel_dilation
    (c w v : ℂ) (hc : c ≠ 0) (hw : w ≠ 0) (hv : v ≠ 0) (hsep : w ≠ v) :
    gffKernel (c * w) (c * v) -
      originRadialCovariance (-Real.log ‖c * w‖) (c * v) =
        gffKernel w v - originRadialCovariance (-Real.log ‖w‖) v := by
  have hsep' : c * w ≠ c * v := by
    ring_nf at * <;> aesop
  rw [origin_lateralKernel_normalized (mul_ne_zero hc hw) (mul_ne_zero hc hv) hsep',
    origin_lateralKernel_normalized hw hv hsep,
    origin_lateral_normalized_separation_dilation c w v hc]

end DOZZ.Proofs
