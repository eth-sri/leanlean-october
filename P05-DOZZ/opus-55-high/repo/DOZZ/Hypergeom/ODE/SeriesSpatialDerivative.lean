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
section
variable (a b c : ℂ) (n : ℕ)

private theorem ordinaryHypergeometricCoefficient_derivative_shift (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    ((n + 1 : ℂ) * ordinaryHypergeometricCoefficient a b c (n + 1)) =
      (a * b / c) * ordinaryHypergeometricCoefficient (a + 1) (b + 1) (c + 1) n := by
  have hc0 : c ≠ 0 := by aesop
  have hcShift : ∀ k : ℕ, c + 1 ≠ -(k : ℂ) := by
    intro k h
    apply hc (k + 1)
    grind
  have hcp1 : (ascPochhammer ℂ n).eval (c + 1) ≠ 0 :=
    ordinaryHypergeometric_pochhammer_denominator_ne_zero n hcShift
  have hfact : ((n + 1).factorial : ℂ) = (n + 1 : ℂ) * (n.factorial : ℂ) := by
    norm_cast
  have hfact0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hshift (x : ℂ) :
      (ascPochhammer ℂ (n + 1)).eval x =
        x * (ascPochhammer ℂ n).eval (x + 1) := by
    rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X]
    simp
  simp only [ordinaryHypergeometricCoefficient]
  rw [hfact, hshift a, hshift b, hshift c]
  field_simp [hc0, hcp1, hfact0]

private theorem ordinaryHypergeometricSeries_coeff' :
    (ordinaryHypergeometricSeries ℂ a b c).coeff n =
      ordinaryHypergeometricCoefficient a b c n := by
  change ordinaryHypergeometricSeries ℂ a b c n (fun _ => 1) = _
  rw [ordinaryHypergeometricSeries_apply_eq]
  simp

end

private theorem ordinaryHypergeometricSeries_derivSeries_eq (a b c : ℂ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    gaussFirstDerivativeSeries a b c =
      (a * b / c) • ordinaryHypergeometricSeries ℂ (a + 1) (b + 1) (c + 1) := by
  apply FormalMultilinearSeries.ext
  intro n
  apply ContinuousMultilinearMap.ext_ring
  change (gaussFirstDerivativeSeries a b c).coeff n =
    ((a * b / c) • ordinaryHypergeometricSeries ℂ _ _ _).coeff n
  rw [DOZZ.Proofs.gaussSeriesCoeff_smul', DOZZ.Proofs.gaussFirstDerivativeSeries_coeff,
    ordinaryHypergeometricSeries_coeff']
  simp
  rw [ordinaryHypergeometricCoefficient_derivative_shift a b c n hc]

/-- At every point of the open unit disk, the spatial derivative is the shifted Gauss series. -/
theorem ordinaryHypergeometric_hasDerivAt_unitDisk (a b c z : ℂ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    HasDerivAt (ordinaryHypergeometric a b c)
      (a * b / c * ordinaryHypergeometric (a + 1) (b + 1) (c + 1) z) z := by
  let S := ordinaryHypergeometricSeries ℂ a b c
  have hznorm : ‖z‖₊ < 1 := by exact_mod_cast hz
  have hz' : z ∈ Metric.eball 0 1 := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm, dist_zero_right] using
      (ENNReal.coe_lt_coe.mpr hznorm)
  have hle : (1 : ENNReal) ≤ S.radius := by exact_mod_cast (ordinaryHypergeometricSeries_one_le_radius a b c hc)
  have hpower : HasFPowerSeriesOnBall (ordinaryHypergeometric a b c) S 0 1 := by
    have hsum : ordinaryHypergeometric a b c = S.sum := rfl
    exact S.hasFPowerSeriesOnBall (ordinaryHypergeometricSeries_radius_pos a b c hc) |>.mono (by norm_num) hle
  let evalOne : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ 1
  have hprimeEq : (fun w => evalOne (fderiv ℂ (ordinaryHypergeometric a b c) w)) =
      deriv (ordinaryHypergeometric a b c) := by
    rfl
  have hprimeFun : HasFPowerSeriesOnBall
      (fun w => evalOne _)
      (evalOne.compFormalMultilinearSeries S.derivSeries) 0 1 := (evalOne.comp_hasFPowerSeriesOnBall hpower.fderiv)
  have hprime : HasFPowerSeriesOnBall (deriv (ordinaryHypergeometric a b c))
      (gaussFirstDerivativeSeries a b c) 0 1 := by
    assumption
  have hderivValue : deriv (ordinaryHypergeometric a b c) z =
      a * b / c * ordinaryHypergeometric (a + 1) (b + 1) (c + 1) z := by
    calc
      deriv _ z =
          (gaussFirstDerivativeSeries a b c).sum z := by simpa using hprime.sum hz'
      _ = ((a * b / c) •
          ordinaryHypergeometricSeries ℂ _ _ _).sum z := by
        rw [(ordinaryHypergeometricSeries_derivSeries_eq a b c hc)]
      _ = a * b / c * ordinaryHypergeometric _ _ _ z := by
        rw [← FormalMultilinearSeries.const_smul_sum_apply]
        simp only [smul_eq_mul]
        rfl
  have hAt :=
    hpower.analyticAt_of_mem hz' |>.differentiableAt
  have hresult := hAt.hasDerivAt
  rwa [hderivValue] at hresult

end DOZZ.Proofs
