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

@[expose] public section

open Filter Set Topology

namespace DOZZ.Proofs

section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
include hH

/-- A family characterized by its ordinary-series germ solves the Gauss equation on the common
principal cut plane. The local series equation is extended by analytic uniqueness. -/
theorem gauss_family_holomorphicOperator_eq_zero (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c (H a b c) z = 0 := by
  have h := hH a b c hc
  have hf := (h.1.analyticOnNhd gaussSlitPlane_isOpen).mono gaussCutPlane_subset_gaussSlitPlane
  have hres : AnalyticOnNhd ℂ (gaussHolomorphicOperator a b c (H a b c)) gaussCutPlane := by
    have hf₁ := hf.deriv
    have hf₂ := hf₁.deriv
    unfold gaussHolomorphicOperator
    fun_prop
  have he : (Metric.ball (0 : ℂ) 1).EqOn (H a b c) (ordinaryHypergeometric a b c) :=
    fun z hz => h.2 z (by simpa [Metric.mem_ball] using hz)
  have he₁ := he.deriv Metric.isOpen_ball
  have he₂ := he₁.deriv Metric.isOpen_ball
  have hm : (1 / 2 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by norm_num [Metric.mem_ball]
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hres (g := fun _ => 0) (by fun_prop)
    gaussCutPlane_isPreconnected (z₀ := 1 / 2) (by norm_num [gaussCutPlane]) ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds hm] with z hz
  simpa only [gaussHolomorphicOperator, he hz, he₁ hz, he₂ hz] using
    ordinaryHypergeometric_gaussEquation_on_unitDisk a b c hc z (by simpa [Metric.mem_ball] using hz)

/-- The unpowered basis function at zero solves the Gauss equation on the common cut plane. -/
theorem gaussFMinus_holomorphicOperator_eq_zero (hc : ∀ n : ℤ, c ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c (gaussFMinus H a b c) z = 0 :=
  gauss_family_holomorphicOperator_eq_zero hH a b c (parameter_ne_nat_neg_of_ne_int hc)

end

end DOZZ.Proofs
