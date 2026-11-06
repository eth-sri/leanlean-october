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
section
variable (d : Nat)

/-- The ABK unit ball is the preimage of Mathlib's Euclidean unit ball under `toLp`. -/
theorem preimage_toLp_two_unitBall :
    (fun x : Vec d => (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))) ⁻¹'
        Metric.ball 0 (1 : ℝ) =
      abkUnitBall d := by
  ext x
  simp only [Set.mem_preimage, Metric.mem_ball, abkUnitBall, abkBall,
    Set.mem_ofPred_eq]
  rw [dist_eq_norm, sub_zero, norm_toLp_two_eq_euclideanNorm]
section
variable (hd : 0 < d)
include hd

/-- Exact Lebesgue volume of the ABK Euclidean unit ball, in `ENNReal` form. -/
theorem volume_abkUnitBall :
    (volume : Measure (Vec d)) (abkUnitBall d) =
      ENNReal.ofReal (Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1)) := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [← preimage_toLp_two_unitBall d]
  rw [(PiLp.volume_preserving_toLp (Fin d)).measure_preimage
    measurableSet_ball.nullMeasurableSet]
  have hvol :=
    EuclideanSpace.volume_ball (Fin d) 0 1
  simp_all

/-- Exact real-valued volume of the ABK Euclidean unit ball. -/
theorem abkUnitBallVolume_eq_sqrt_pi_div_gamma :
    abkUnitBallVolume d =
      Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1) := by
  have harg : 0 < (d : ℝ) / 2 + 1 := by positivity
  have hnonneg :
      0 ≤ Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1) := by
    positivity
  rw [abkUnitBallVolume, volume_abkUnitBall d hd]
  simp_all

end

/-- Convert the power of `sqrt π` in the Euclidean ball volume to a real power of `π`. -/
theorem sqrt_pi_pow_eq_pi_rpow_half_mul :
    Real.sqrt Real.pi ^ d = Real.pi ^ ((d : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow]
  calc
    (Real.pi ^ (1 / (2 : ℝ))) ^ d
        = Real.pi ^ ((1 / (2 : ℝ)) * (d : ℝ)) := by
            rw [← Real.rpow_mul_natCast Real.pi_pos.le (1 / (2 : ℝ)) d]
    _ = Real.pi ^ ((d : ℝ) / 2) := by ring_nf

/-- Gamma-function form of the ABK covariance prefactor
`d |B_1| / (2π)^d`. -/
theorem abkLGFCovarianceConstant_eq_gammaFormula (hd : 0 < d) :
    abkLGFCovarianceConstant d =
      2 ^ (1 - (d : ℝ)) * Real.pi ^ (-(d : ℝ) / 2) /
        Real.Gamma ((d : ℝ) / 2) := by
  let s := (d : ℝ) / 2
  have hs_pos : 0 < s := by
    positivity
  have hs_ne : s ≠ 0 := hs_pos.ne'
  have hgamma_ne : Real.Gamma s ≠ 0 :=
    by positivity
  have hd_real_ne : (d : ℝ) ≠ 0 := by positivity
  have hgamma : Real.Gamma ((d : ℝ) / 2 + 1) =
      ((d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2) := by
    exact Real.Gamma_add_one hs_ne
  have htwo :
      2 ^ (1 - (d : ℝ)) = (2 : ℝ) / 2 ^ d := by
    calc
      2 ^ (1 - (d : ℝ))
          = (2 : ℝ) ^ (1 : ℝ) / (2 : ℝ) ^ (d : ℝ) :=
              Real.rpow_sub (by norm_num : (0 : ℝ) < 2) 1 (d : ℝ)
      _ = (2 : ℝ) / 2 ^ d := by simp
  have hpi :
      Real.pi ^ (-(d : ℝ) / 2) =
        Real.pi ^ ((d : ℝ) / 2) / Real.pi ^ d := by
    have hexp : -(d : ℝ) / 2 = (d : ℝ) / 2 - (d : ℝ) := by ring
    calc
      Real.pi ^ (-(d : ℝ) / 2)
          = Real.pi ^ ((d : ℝ) / 2 - (d : ℝ)) := by ring
      _ = Real.pi ^ ((d : ℝ) / 2) / Real.pi ^ (d : ℝ) :=
            Real.rpow_sub Real.pi_pos ((d : ℝ) / 2) (d : ℝ)
      _ = Real.pi ^ ((d : ℝ) / 2) / Real.pi ^ d := by simp
  rw [abkLGFCovarianceConstant, abkUnitBallVolume_eq_sqrt_pi_div_gamma d hd,
    sqrt_pi_pow_eq_pi_rpow_half_mul d, hgamma, mul_pow, htwo, hpi]
  field_simp

end

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
    exact ENNReal.toReal_nonneg
  have hnum :=
    mul_nonneg (Nat.cast_nonneg d) hvol
  have hden : 0 ≤ abkM0 ζ * (2 * Real.pi) ^ d :=
    mul_nonneg (le_of_lt (abkM0_pos ζ))
      (le_of_lt (pow_pos (mul_pos (by norm_num) Real.pi_pos) d))
  unfold abkNormalizationRadicand
  positivity

end GaussianFields

end
