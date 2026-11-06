/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.SeriesEquation
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Spatial differentiation of the ordinary Gauss series, with its parameter shift. -/

@[expose] public section

open Polynomial FormalMultilinearSeries

namespace DOZZ.Proofs






/-- At every point of the open unit disk, the spatial derivative is the shifted Gauss series. -/
theorem ordinaryHypergeometric_hasDerivAt_unitDisk a b c z
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    HasDerivAt (ordinaryHypergeometric a b c)
      (a * b / c * ordinaryHypergeometric (a + 1) (b + 1) (c + 1) z) z := by
  have ordinaryHypergeometricSeries_derivSeries_eq : gaussFirstDerivativeSeries a b c = (a * b / c) • ordinaryHypergeometricSeries ℂ (a + 1) (b + 1) (c + 1) := by
    have formalSeries_coeff_smul' (x : ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) : (x • p).coeff n = x • p.coeff n := rfl
    have gaussFirstDerivativeSeries_coeff' a b c n : (gaussFirstDerivativeSeries a b c).coeff n = (n + 1 : ℂ) * ordinaryHypergeometricCoefficient a b c (n + 1) := by
      change ((gaussSeriesAtZero a b c).derivSeries.coeff n) 1 = _
      rw [FormalMultilinearSeries.derivSeries_coeff_one]
      have hcoeff : (gaussSeriesAtZero a b c).coeff (n + 1) =
          ordinaryHypergeometricCoefficient a b c (n + 1) := by
        change ordinaryHypergeometricSeries ℂ a b c (n + 1) (fun _ => (1 : ℂ)) = _
        rw [ordinaryHypergeometricSeries_apply_eq]
        simp [ordinaryHypergeometricCoefficient]
      rw [hcoeff]
      simp only [nsmul_eq_mul, Nat.cast_succ]
    have ordinaryHypergeometricSeries_coeff' a b c n : (ordinaryHypergeometricSeries ℂ a b c).coeff n = ordinaryHypergeometricCoefficient a b c n := by
      change ordinaryHypergeometricSeries ℂ a b c n (fun _ => (1 : ℂ)) = _
      rw [ordinaryHypergeometricSeries_apply_eq]
      simp [ordinaryHypergeometricCoefficient]
    have ordinaryHypergeometricCoefficient_derivative_shift (n : ℕ) (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) : ((n + 1 : ℂ) * ordinaryHypergeometricCoefficient a b c (n + 1)) = (a * b / c) * ordinaryHypergeometricCoefficient (a + 1) (b + 1) (c + 1) n := by
      have hcShift : ∀ k : ℕ, c + 1 ≠ -(k : ℂ) := by
        intro k h
        apply hc (k + 1)
        push_cast at h ⊢
        linear_combination h
      have hshift (x : ℂ) :
          (ascPochhammer ℂ (n + 1)).eval x =
            x * (ascPochhammer ℂ n).eval (x + 1) := by
        rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X]
        exact congrArg (fun y : ℂ => x * y) (by simp)
      simp only [ordinaryHypergeometricCoefficient]
      rw [(show ((n + 1).factorial : ℂ) = (n + 1 : ℂ) * (n.factorial : ℂ) by exact_mod_cast Nat.factorial_succ n), hshift a, hshift b, hshift c]
      field_simp [(by simpa using hc 0), (ordinaryHypergeometric_pochhammer_denominator_ne_zero n hcShift), (by exact_mod_cast Nat.factorial_ne_zero n)]
    apply FormalMultilinearSeries.ext
    intro n
    apply ContinuousMultilinearMap.ext_ring
    change (gaussFirstDerivativeSeries a b c).coeff n =
      ((a * b / c) • ordinaryHypergeometricSeries ℂ (a + 1) (b + 1) (c + 1)).coeff n
    rw [formalSeries_coeff_smul', gaussFirstDerivativeSeries_coeff',
      ordinaryHypergeometricSeries_coeff']
    simp only [smul_eq_mul]
    rw [ordinaryHypergeometricCoefficient_derivative_shift n hc]
  let S := ordinaryHypergeometricSeries ℂ a b c
  have hz' : z ∈ Metric.eball (0 : ℂ) 1 := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm, dist_zero_right] using
      (ENNReal.coe_lt_coe.mpr (by exact_mod_cast hz))
  have hpower : HasFPowerSeriesOnBall (ordinaryHypergeometric a b c) S 0 1 := by
    rw [(rfl : ordinaryHypergeometric a b c = S.sum)]
    exact S.hasFPowerSeriesOnBall (ordinaryHypergeometricSeries_radius_pos a b c hc) |>.mono (by norm_num) (by exact_mod_cast (ordinaryHypergeometricSeries_one_le_radius a b c hc))
  let evalOne : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ 1
  have hprimeFun : HasFPowerSeriesOnBall
      (fun w => evalOne (fderiv ℂ (ordinaryHypergeometric a b c) w))
      (evalOne.compFormalMultilinearSeries S.derivSeries) 0 1 := (evalOne.comp_hasFPowerSeriesOnBall hpower.fderiv)
  rw [(show (fun w => evalOne (fderiv ℂ (ordinaryHypergeometric a b c) w)) = deriv (ordinaryHypergeometric a b c) by funext w; exact fderiv_apply_one_eq_deriv)] at hprimeFun
  have hderivValue : deriv (ordinaryHypergeometric a b c) z =
      a * b / c * ordinaryHypergeometric (a + 1) (b + 1) (c + 1) z := by
    calc
      deriv (ordinaryHypergeometric a b c) z =
          (gaussFirstDerivativeSeries a b c).sum z := by simpa using (show HasFPowerSeriesOnBall (deriv (ordinaryHypergeometric a b c)) (gaussFirstDerivativeSeries a b c) 0 1 by simpa [gaussFirstDerivativeSeries, gaussSeriesAtZero, S] using hprimeFun).sum hz'
      _ = ((a * b / c) •
          ordinaryHypergeometricSeries ℂ (a + 1) (b + 1) (c + 1)).sum z := by
        rw [(ordinaryHypergeometricSeries_derivSeries_eq)]
      _ = a * b / c * ordinaryHypergeometric (a + 1) (b + 1) (c + 1) z := by
        rw [← FormalMultilinearSeries.const_smul_sum_apply]
        simp only [smul_eq_mul]
        rfl
  have hresult := (hpower.analyticAt_of_mem hz' |>.differentiableAt).hasDerivAt
  rw [hderivValue] at hresult
  exact hresult

end DOZZ.Proofs
