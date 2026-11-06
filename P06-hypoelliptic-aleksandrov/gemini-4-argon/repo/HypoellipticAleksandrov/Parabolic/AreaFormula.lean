module

public import HypoellipticAleksandrov.Measure.TimeVelocity
public import HypoellipticAleksandrov.Parabolic.Jacobian
public import PDEFoundation.Measure.BallVolume
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# One-sided area formula for the parabolic normal map

This module records the exact product-volume normalization of the
slope--intercept wedge and specializes the one-sided area formula to the
parabolic normal map.  The `TimeVelocity` volume is the product
Lebesgue measure; no competing Haar instance is introduced.  The area bound
does not assume injectivity.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped ENNReal

/- The exact product-volume normalization of the slope--intercept wedge. -/
theorem volume_slopeInterceptWedge_eq {d : ℕ} {M : ℝ} (hM : 0 < M) :
    volume (slopeInterceptWedge d M) =
      ENNReal.ofReal ((M / 4) ^ (d + 1)) *
        volume (PDE.euclideanBall (0 : PDE.Vec d) 1) := by
  have _h_inl_10 : volume (slopeInterceptWedge d M) =
      ENNReal.ofReal (M / 4) *
        (ENNReal.ofReal ((M / 4) ^ d) *
          volume (PDE.euclideanBall (0 : PDE.Vec d) 1)) := by
      unfold slopeInterceptWedge
      have hM4 : 0 < M / 4 := div_pos hM (by norm_num)
      have hinterval : 3 * M / 4 - M / 2 = M / 4 := by ring
      rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, hinterval,
        PDE.volume_euclideanBall_eq_unit_mul_of_pos (0 : PDE.Vec d) hM4]

    /- The wedge volume with its time and velocity scaling combined into one power. -/
  rw [_h_inl_10]
  have hM4 : 0 ≤ M / 4 := (div_pos hM (by norm_num)).le
  calc
    ENNReal.ofReal (M / 4) *
        (ENNReal.ofReal ((M / 4) ^ d) * volume (PDE.euclideanBall (0 : PDE.Vec d) 1)) =
        (ENNReal.ofReal (M / 4) * ENNReal.ofReal ((M / 4) ^ d)) *
          volume (PDE.euclideanBall (0 : PDE.Vec d) 1) := by
      rw [mul_assoc]
    _ = ENNReal.ofReal ((M / 4) * (M / 4) ^ d) *
          volume (PDE.euclideanBall (0 : PDE.Vec d) 1) := by
      rw [← ENNReal.ofReal_mul hM4]
    _ = ENNReal.ofReal ((M / 4) ^ (d + 1)) *
          volume (PDE.euclideanBall (0 : PDE.Vec d) 1) := by
      congr 2
      rw [pow_succ]
      ring

/- The one-sided area formula for the actual parabolic normal map on its sign set.

No injectivity or finiteness hypothesis is required. -/
end HypoellipticAleksandrov.Parabolic
