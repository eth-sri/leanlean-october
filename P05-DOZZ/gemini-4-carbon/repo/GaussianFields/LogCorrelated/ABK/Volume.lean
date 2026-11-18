/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import GaussianFields.LogCorrelated.ABK.Constants

/-!
# GaussianFields.LogCorrelated/ABK/Volume

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory
open scoped ENNReal Topology

namespace GaussianFields

/-- The Mathlib `EuclideanSpace` norm of `WithLp.toLp 2 x` is the project
Euclidean norm of `x`. -/
theorem norm_toLp_two_eq_euclideanNorm {d : Nat} (x : Vec d) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ = euclideanNorm x := by
  rw [EuclideanSpace.norm_eq, euclideanNorm, euclideanNormSq_eq_sum]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [Real.norm_eq_abs, sq_abs]
  ring





/-- Gamma-function form of the ABK covariance prefactor
`d |B_1| / (2π)^d`. -/
theorem abkLGFCovarianceConstant_eq_gammaFormula (d : Nat) (hd : 0 < d) :
    abkLGFCovarianceConstant d =
      2 ^ (1 - (d : ℝ)) * Real.pi ^ (-(d : ℝ) / 2) /
        Real.Gamma ((d : ℝ) / 2) := by
  have sqrt_pi_pow_eq_pi_rpow_half_mul : Real.sqrt Real.pi ^ d = Real.pi ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    calc
      (Real.pi ^ (1 / (2 : ℝ))) ^ d
          = Real.pi ^ ((1 / (2 : ℝ)) * (d : ℝ)) := by
              rw [← Real.rpow_mul_natCast Real.pi_pos.le (1 / (2 : ℝ)) d]
      _ = Real.pi ^ ((d : ℝ) / 2) := by ring_nf
  have volume_abkUnitBall : (volume : Measure (Vec d)) (abkUnitBall d) =
        ENNReal.ofReal (Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1)) := by
    have preimage_toLp_two_unitBall : (fun x : Vec d => (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))) ⁻¹'
            Metric.ball 0 (1 : ℝ) =
          abkUnitBall d := by
      ext x
      simp only [Set.mem_preimage, Metric.mem_ball, abkUnitBall, abkBall,
        Set.mem_ofPred_eq]
      rw [dist_eq_norm, sub_zero]
      rw [norm_toLp_two_eq_euclideanNorm]
    have := Fin.pos_iff_nonempty.mp hd
    rw [← preimage_toLp_two_unitBall]
    rw [(PiLp.volume_preserving_toLp (Fin d)).measure_preimage
      measurableSet_ball.nullMeasurableSet]
    simpa [Fintype.card_fin] using EuclideanSpace.volume_ball (Fin d) (0 : EuclideanSpace ℝ (Fin d)) (1 : ℝ)
  have abkUnitBallVolume_eq_sqrt_pi_div_gamma : abkUnitBallVolume d =
        Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1) := by
    have harg : 0 < (d : ℝ) / 2 + 1 := by positivity
    have hnonneg :
        0 ≤ Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1) := div_nonneg (pow_nonneg (Real.sqrt_nonneg _) d)
        (Real.Gamma_pos_of_pos harg).le
    rw [abkUnitBallVolume, volume_abkUnitBall]
    exact ENNReal.toReal_ofReal hnonneg
  have hs_pos : 0 < ((d : ℝ) / 2) := by positivity
  have hd_real_ne : (d : ℝ) ≠ 0 := by positivity
  have hgamma : Real.Gamma ((d : ℝ) / 2 + 1) =
      ((d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2) := Real.Gamma_add_one (hs_pos.ne')
  have htwo :
      2 ^ (1 - (d : ℝ)) = (2 : ℝ) / 2 ^ d := by
    refine (Real.rpow_sub (by norm_num : (0 : ℝ) < 2) 1 (d : ℝ)).trans (?_)
    rw [Real.rpow_one, Real.rpow_natCast]
  have hpi :
      Real.pi ^ (-(d : ℝ) / 2) =
        Real.pi ^ ((d : ℝ) / 2) / Real.pi ^ d := by
    have hexp : -(d : ℝ) / 2 = (d : ℝ) / 2 - (d : ℝ) := by ring
    calc
      Real.pi ^ (-(d : ℝ) / 2)
          = Real.pi ^ ((d : ℝ) / 2 - (d : ℝ)) := by rw [hexp]
      _ = Real.pi ^ ((d : ℝ) / 2) / Real.pi ^ (d : ℝ) :=
            Real.rpow_sub Real.pi_pos ((d : ℝ) / 2) (d : ℝ)
      _ = Real.pi ^ ((d : ℝ) / 2) / Real.pi ^ d := by rw [Real.rpow_natCast]
  rw [abkLGFCovarianceConstant, abkUnitBallVolume_eq_sqrt_pi_div_gamma,
    sqrt_pi_pow_eq_pi_rpow_half_mul, hgamma, mul_pow, htwo, hpi]
  field_simp [hd_real_ne, (Real.Gamma_pos_of_pos hs_pos).ne', Real.pi_ne_zero, two_ne_zero]

/-- In two dimensions the ABK covariance prefactor is `1/(2π)`. -/
theorem abkLGFCovarianceConstant_two :
    abkLGFCovarianceConstant 2 = (2 * Real.pi)⁻¹ := by
  rw [abkLGFCovarianceConstant_eq_gammaFormula 2 (by norm_num)]
  norm_num
  rw [Real.rpow_neg_one]
  ring

/-- The canonical ABK normalization radicand is nonnegative. -/
theorem abkNormalizationRadicand_nonneg {d : Nat} (ζ : ABKCutoff d) :
    0 ≤ abkNormalizationRadicand ζ := by
  have hvol : 0 ≤ abkUnitBallVolume d := by
    unfold abkUnitBallVolume
    exact ENNReal.toReal_nonneg
  have hden :=
    mul_nonneg (le_of_lt (abkM0_pos ζ))
      (le_of_lt (pow_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) d))
  unfold abkNormalizationRadicand
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg d) hvol) hden

end GaussianFields

end
