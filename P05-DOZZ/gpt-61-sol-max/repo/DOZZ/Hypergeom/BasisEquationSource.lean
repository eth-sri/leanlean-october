/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.BasisRegularity
public import DOZZ.Hypergeom.ODE.SeriesEquation
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! The characterization of the principal family forces the Gauss equation on the cut plane. -/

public section

open Filter Set Topology

namespace DOZZ.Proofs

private theorem gaussSlitPlane_isOpen : IsOpen gaussSlitPlane := (isOpen_compl_singleton.preimage Complex.continuous_im).union
    (isOpen_Iio.preimage Complex.continuous_re)

private theorem gaussCutPlane_isPreconnected : IsPreconnected gaussCutPlane := by
  have hstar := gaussCutPlane_starConvex
  have hbase : (1 / 2 : ℂ) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  exact hstar.isPathConnected hbase |>.isConnected.isPreconnected

variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)

include H hH a b c in
/-- A family characterized by its ordinary-series germ solves the Gauss equation on the common
principal cut plane. The local series equation is extended by analytic uniqueness. -/
theorem gauss_family_holomorphicOperator_eq_zero
     (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c (H a b c) z = 0 := by
  let f : ℂ → ℂ := H a b c
  let g : ℂ → ℂ := ordinaryHypergeometric a b c
  have hchar : IsGaussHypergeometric a b c f := hH a b c hc
  have hF  := hchar.1.analyticOnNhd gaussSlitPlane_isOpen
  have hF'  := hF.deriv

  have hresAnalytic : AnalyticOnNhd ℂ
      (fun z => gaussHolomorphicOperator a b c f z) gaussCutPlane := by
    intro z hz
    have hzslit  := gaussCutPlane_subset_gaussSlitPlane hz
    have hfz := hF z hzslit


    dsimp [gaussHolomorphicOperator]
    fun_prop
  have hEq : (Metric.ball (0 : ℂ) 1).EqOn f g := by
    intro z hz
    have hznorm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    exact hchar.2 z hznorm
  have hEq'  :=
    hEq.deriv Metric.isOpen_ball
  have hEq''  :=
    hEq'.deriv Metric.isOpen_ball
  have hresZeroDisk : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      gaussHolomorphicOperator a b c f z = 0 := by
    intro z hz
    have h := ordinaryHypergeometric_gaussEquation_on_unitDisk a b c hc z ?_
    · simpa [f, g, gaussHolomorphicOperator, hEq hz, hEq' hz, hEq'' hz] using h
    simp_all
  have hzeroBase : (1 / 2 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    norm_num
  have hcutBase : (1 / 2 : ℂ) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  have hzeroNear : (fun z => gaussHolomorphicOperator a b c f z) =ᶠ[𝓝 (1 / 2 : ℂ)]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [Metric.ball_mem_nhds (1 / 2 : ℂ) (by norm_num : 0 < (1 : ℝ) / 4)]
      with z hz
    apply hresZeroDisk z
    have hdist  := Metric.mem_ball.mp hz
    rw [Metric.mem_ball, dist_zero_right]
    have hnorm : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    calc
      ‖z‖ ≤ ‖z - (1 / 2 : ℂ)‖ + ‖(1 / 2 : ℂ)‖ := by
        simpa [sub_add_cancel] using norm_add_le (z - (1 / 2 : ℂ)) (1 / 2 : ℂ)
      _ < 1 / 4 + 1 / 2 := by rw [dist_eq_norm] at hdist; rw [hnorm]; linarith
      _ < 1 := by norm_num
  have hresZero  :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hresAnalytic
      (by fun_prop) gaussCutPlane_isPreconnected hcutBase hzeroNear
  intro z hz
  exact hresZero hz

include H hH a b c in
/-- The unpowered basis function at zero solves the Gauss equation on the common cut plane. -/
theorem gaussFMinus_holomorphicOperator_eq_zero
     (hc : ∀ n : ℤ, c ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c (gaussFMinus H a b c) z = 0 := by
  have hcNat : ∀ n : ℕ, c ≠ -(n : ℂ) := by
    intro n heq
    apply hc (-(n : ℤ))
    exact heq.trans (by simp)
  exact gauss_family_holomorphicOperator_eq_zero hH a b c hcNat

end DOZZ.Proofs
