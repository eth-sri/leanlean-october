/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.SeriesRecurrence
public import DOZZ.Hypergeom.ODE.GaussSystem
public import DOZZ.Hypergeom.Series
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! The ordinary Gauss series satisfies its scalar equation on the unit disk. -/

@[expose] public section

open Polynomial FormalMultilinearSeries

namespace DOZZ.Proofs

/-- The ordinary Gauss power series, viewed as a formal multilinear series. -/
noncomputable def gaussSeriesAtZero (a b c : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  ordinaryHypergeometricSeries ℂ a b c

/-- The scalar power series for the derivative of the ordinary Gauss series. -/
noncomputable def gaussFirstDerivativeSeries (a b c : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
    (gaussSeriesAtZero a b c).derivSeries

/-- The power series for `z` times the derivative of the ordinary Gauss series. -/
noncomputable def gaussZFirstDerivativeSeries (a b c : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  (gaussSeriesAtZero a b c).derivSeries.unshift 0

/-- The series for `(1-z)` times the derivative, formed by subtraction. -/
noncomputable def gaussOneSubZDerivativeSeries (a b c : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  gaussFirstDerivativeSeries a b c - gaussZFirstDerivativeSeries a b c

/-- The power series for `z` times the derivative of `(1-z)f'`. -/
noncomputable def gaussZOneSubZDerivativeDerivativeSeries (a b c : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  (gaussOneSubZDerivativeSeries a b c).derivSeries.unshift 0

/-- Formal series for the Gauss differential residual written using the Euler derivative. -/
noncomputable def gaussEquationResidualSeries (a b c : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  gaussZOneSubZDerivativeDerivativeSeries a b c -
    (a + b) • gaussZFirstDerivativeSeries a b c +
    c • gaussFirstDerivativeSeries a b c -
    (a * b) • gaussSeriesAtZero a b c
section
variable (a b c : ℂ)
section
variable (n : ℕ)

private theorem gaussSeriesCoeff_eq :
    (gaussSeriesAtZero a b c).coeff n = ordinaryHypergeometricCoefficient a b c n := by
  change ordinaryHypergeometricSeries ℂ a b c n (fun _ => 1) = _
  rw [ordinaryHypergeometricSeries_apply_eq]
  simp

theorem gaussFirstDerivativeSeries_coeff :
    (gaussFirstDerivativeSeries a b c).coeff n =
      (n + 1 : ℂ) * ordinaryHypergeometricCoefficient a b c (n + 1) := by
  change ((gaussSeriesAtZero a b c).derivSeries.coeff n) 1 = _
  rw [FormalMultilinearSeries.derivSeries_coeff_one]
  have hp := gaussSeriesCoeff_eq a b c (n + 1)
  simp_all

end

private theorem gaussZFirstDerivativeSeries_coeff_zero :
    (gaussZFirstDerivativeSeries a b c).coeff 0 = 0 := by
  rfl
section
variable (n : ℕ)

private theorem gaussZFirstDerivativeSeries_coeff_succ :
    (gaussZFirstDerivativeSeries a b c).coeff (n + 1) =
      (n + 1 : ℂ) * ordinaryHypergeometricCoefficient a b c (n + 1) := by
  change ((gaussSeriesAtZero a b c).derivSeries.coeff n) 1 = _
  rw [FormalMultilinearSeries.derivSeries_coeff_one]
  have hp := gaussSeriesCoeff_eq a b c (n + 1)
  simp_all

private theorem gaussZFirstDerivativeSeries_coeff :
    (gaussZFirstDerivativeSeries a b c).coeff n =
      (n : ℂ) * ordinaryHypergeometricCoefficient a b c n := by
  cases n with
  | zero => simp [gaussZFirstDerivativeSeries_coeff_zero]
  | succ n => simpa [Nat.cast_succ] using gaussZFirstDerivativeSeries_coeff_succ a b c n

private theorem gaussOneSubZDerivativeSeries_coeff :
    (gaussOneSubZDerivativeSeries a b c).coeff n =
      ((n + 1 : ℂ) * ordinaryHypergeometricCoefficient a b c (n + 1) -
        (n : ℂ) * ordinaryHypergeometricCoefficient a b c n) := by
  change (gaussFirstDerivativeSeries a b c).coeff n -
    (gaussZFirstDerivativeSeries a b c).coeff n = _
  rw [gaussFirstDerivativeSeries_coeff, gaussZFirstDerivativeSeries_coeff]

private theorem gaussZOneSubZDerivativeDerivativeSeries_coeff :
  (gaussZOneSubZDerivativeDerivativeSeries a b c).coeff n =
      (n : ℂ) * (gaussOneSubZDerivativeSeries a b c).coeff n := by
  cases n with
  | zero =>
      simp
      change ((gaussOneSubZDerivativeSeries a b c).derivSeries.unshift 0)
        0 (fun _ => 1) = 0
      simp only [FormalMultilinearSeries.unshift]
      simp
  | succ n =>
      change ((gaussOneSubZDerivativeSeries a b c).derivSeries.coeff n) 1 = _
      simp

end

end
section
variable {p q : FormalMultilinearSeries ℂ ℂ ℂ} (n : ℕ)

private theorem gaussSeriesCoeff_add' :
    (p + q).coeff n = p.coeff n + q.coeff n := rfl

private theorem gaussSeriesCoeff_sub' :
    (p - q).coeff n = p.coeff n - q.coeff n := rfl

end

theorem gaussSeriesCoeff_smul' (x : ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (n : ℕ) : (x • p).coeff n = x • p.coeff n := rfl
section
variable (a b c : ℂ)

private theorem gaussEquationResidualSeries_coeff (n : ℕ) :
    (gaussEquationResidualSeries a b c).coeff n =
      ((n + 1 : ℂ) * ((n : ℂ) + c) * ordinaryHypergeometricCoefficient a b c (n + 1) -
        ((n : ℂ) + a) * ((n : ℂ) + b) * ordinaryHypergeometricCoefficient a b c n) := by
  rw [gaussEquationResidualSeries, gaussSeriesCoeff_sub', gaussSeriesCoeff_add',
    gaussSeriesCoeff_sub', gaussSeriesCoeff_smul', gaussSeriesCoeff_smul',
    gaussSeriesCoeff_smul', gaussZOneSubZDerivativeDerivativeSeries_coeff,
    gaussOneSubZDerivativeSeries_coeff, gaussZFirstDerivativeSeries_coeff,
    gaussFirstDerivativeSeries_coeff, gaussSeriesCoeff_eq]
  ring
section
variable (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
include hc

private theorem gaussEquationResidualSeries_eq_zero : gaussEquationResidualSeries a b c = 0 := by
  apply FormalMultilinearSeries.ext
  intro n
  apply FormalMultilinearSeries.coeff_eq_zero.mp
  rw [gaussEquationResidualSeries_coeff]
  exact sub_eq_zero.mpr (ordinaryHypergeometricCoefficient_gauss_recurrence a b c n hc)

private theorem hasFPowerSeriesOnBall_ordinaryHypergeometric :
    HasFPowerSeriesOnBall (ordinaryHypergeometric a b c)
      (gaussSeriesAtZero a b c) 0 1 := by
  let p := gaussSeriesAtZero a b c
  have hpos :=
    ordinaryHypergeometricSeries_radius_pos a b c hc
  have hle : 1 ≤ p.radius := ordinaryHypergeometricSeries_one_le_radius a b c hc
  have hsum : ordinaryHypergeometric a b c = p.sum := by
    rfl
  exact p.hasFPowerSeriesOnBall hpos |>.mono (by norm_num) hle

/-- The ordinary Gauss series is analytic throughout its open unit disk when its denominator
parameter avoids nonpositive integers. -/
theorem ordinaryHypergeometric_analyticOnNhd_unitDisk :
    AnalyticOnNhd ℂ (ordinaryHypergeometric a b c) (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  have hzNorm : ‖z‖ < 1 := by
    simp_all
  have hznorm : ‖z‖₊ < 1 := by exact_mod_cast hzNorm
  have hzball : z ∈ Metric.eball 0 1 := by
    tauto
  exact (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c hc).analyticAt_of_mem hzball

end

end

private theorem fderiv_apply_eq_mul_deriv (f : ℂ → ℂ) (z : ℂ) :
    (fderiv ℂ f z) z = z * deriv f z := by
  simp
section
variable (a b c : ℂ)
section
variable (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
include hc

/-- On the open unit disk, the ordinary series solves the scalar Gauss equation. This is
the origin seed for the first-order continuation system; it includes terminating numerator cases. -/
theorem ordinaryHypergeometric_gaussEquation_on_unitDisk :
    ∀ z : ℂ, ‖z‖ < 1 →
      gaussHolomorphicOperator a b c (ordinaryHypergeometric a b c) z = 0 := by
  let f : ℂ → ℂ := ordinaryHypergeometric a b c
  let g : ℂ → ℂ := fun z => deriv f z - z * deriv f z
  have hf := hasFPowerSeriesOnBall_ordinaryHypergeometric a b c hc
  have hdf := hf.fderiv
  let evalOne : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ 1
  have hfprimeComp := evalOne.comp_hasFPowerSeriesOnBall hdf
  have hfprime_eq : (fun z => evalOne (fderiv ℂ f z)) = deriv f := by
    rfl
  have hfprime : HasFPowerSeriesOnBall (deriv f)
      (evalOne.compFormalMultilinearSeries (gaussSeriesAtZero a b c).derivSeries) 0 1 := by
    assumption
  have hzf : HasFPowerSeriesOnBall (fun z => z * deriv f z)
      (gaussZFirstDerivativeSeries a b c) 0 1 := by
    have h := hdf.unshift (z := 0)
    aesop
  have hzg : HasFPowerSeriesOnBall (fun z =>
      z * deriv g z) (gaussZOneSubZDerivativeDerivativeSeries a b c) 0 1 := by
    have h := (hfprime.sub hzf).fderiv |>.unshift (z := 0)
    aesop
  have hresidual : HasFPowerSeriesOnBall
      (fun z => z * deriv g z - (a + b) • (z * deriv f z) +
        c • deriv f z - (a * b) • f z)
      (gaussEquationResidualSeries a b c) 0 1 := by
    convert (hzg.sub (hzf.const_smul (c := a + b))).add
        (hfprime.const_smul (c := c)) |>.sub (hf.const_smul (c := a * b)) using 1
    rfl
  intro z hz
  have hznorm : ‖z‖₊ < 1 := by exact_mod_cast hz
  have hzball : z ∈ Metric.eball 0 1 := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm, dist_zero_right] using
      (ENNReal.coe_lt_coe.mpr hznorm)
  have hsum := hresidual.sum hzball
  rw [(gaussEquationResidualSeries_eq_zero a b c hc)] at hsum
  have hres : z * deriv g z - (a + b) • (z * deriv f z) +
      c • deriv f z - (a * b) • f z = 0 := by
    simpa [FormalMultilinearSeries.sum] using hsum
  have hfAnalytic := hf.analyticAt_of_mem hzball
  have hfprimeDiff :=
    (hfprime.analyticAt_of_mem hzball).differentiableAt
  have hprod : HasDerivAt (fun w : ℂ => w * deriv f w)
      (deriv f z + z * deriv (deriv f) z) z := by
    have hfun : (fun w : ℂ => w * deriv f w) = (fun w : ℂ => w) * deriv f := by
      funext w
      rfl
    simpa using
      ((hasDerivAt_id z).mul hfprimeDiff.hasDerivAt).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => congrFun hfun w)
  have hgdiff : DifferentiableAt ℂ g z := by
    apply DifferentiableAt.sub hfprimeDiff
      (hprod.differentiableAt)
  have hgderiv : deriv g z =
      deriv (deriv f) z - (deriv f z + z * deriv (deriv f) z) := by
    change deriv (deriv f - fun w => w * deriv f w) z = _
    rw [deriv_sub hfprimeDiff hprod.differentiableAt, hprod.deriv]
  have hsystem : gaussHolomorphicOperator a b c f z =
      z * deriv g z - (a + b) * (z * deriv f z) +
        c * deriv f z - (a * b) * f z := by
    rw [hgderiv]
    simp only [gaussHolomorphicOperator]
    ring
  rw [hsystem]
  simpa [smul_eq_mul] using hres

/-- Away from the singular origin, the ordinary-series state `(f, f')` solves the explicit
first-order Gauss system. -/
theorem ordinaryHypergeometric_state_solves_gaussSystem {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    gaussSystemOperator a b c z
        (ordinaryHypergeometric a b c z, deriv (ordinaryHypergeometric a b c) z) =
      (deriv (ordinaryHypergeometric a b c) z,
        deriv (deriv (ordinaryHypergeometric a b c)) z) := by
  have hz1 : z ≠ 1 := by
    aesop
  have hsystem :=
    (gaussHolomorphicOperator_eq_zero_iff_system_residual_eq_zero a b c
      (ordinaryHypergeometric a b c) hz0 hz1).mp
      (ordinaryHypergeometric_gaussEquation_on_unitDisk a b c hc z hz)
  simp_all

end

end

end DOZZ.Proofs
