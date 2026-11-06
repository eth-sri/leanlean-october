/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosGaussianLaplaceFintype
public import DOZZ.GMC.FiniteChaosMellin
public import DOZZ.Statements.GMC.FiniteChaosMoment
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Negative finite-chaos powers from the finite Laplace comparison. -/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Distributions

namespace DOZZ.Proofs

/-- Integrating the pointwise Mellin formula expresses a negative moment as a weighted integral
of Laplace transforms. Tonelli is applied on the probability space times the positive half-line. -/
theorem nonneg_rpow_neg_lintegral_eq_weighted_laplace
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : Ω → ℝ)
    (hm : ∀ᵐ ω ∂P, 0 ≤ m ω) (hmA : AEMeasurable m P) (q : ℝ) (hq : 0 < q) :
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (m ω)) (-q) ∂P =
      ENNReal.ofReal (1 / Real.Gamma q) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(m ω * t))) ∂P) ∂volume := by
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let c : ℝ≥0∞ := ENNReal.ofReal (1 / Real.Gamma q)
  let f : Ω → ℝ → ℝ≥0∞ := fun ω t =>
    ENNReal.ofReal (t ^ (q - 1) * Real.exp (-(m ω * t)))
  have hc : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hf : AEMeasurable (Function.uncurry f) (P.prod ν) := by
    fun_prop (disch := positivity)
  have hfactor : ∀ᵐ t ∂ν,
      (∫⁻ ω, f ω t ∂P) = ENNReal.ofReal (t ^ (q - 1)) *
        (∫⁻ ω, ENNReal.ofReal (Real.exp (-(m ω * t))) ∂P) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hct : ENNReal.ofReal (t ^ (q - 1)) ≠ ∞ := ENNReal.ofReal_ne_top
    rw [show (fun ω => f ω t) = fun ω => ENNReal.ofReal (t ^ (q - 1)) *
        ENNReal.ofReal (Real.exp (-(m ω * t))) by
          funext ω
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _)] ]
    exact lintegral_const_mul' _ _ hct
  have hpoint : ∀ᵐ ω ∂P,
      ENNReal.rpow (ENNReal.ofReal (m ω)) (-q) =
        c * ∫⁻ t in Ioi (0 : ℝ), f ω t ∂volume := by
    filter_upwards [hm] with ω hω
    exact nonneg_rpow_neg_eq_mellin_lintegral hω hq
  calc
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (m ω)) (-q) ∂P =
        ∫⁻ ω, c * (∫⁻ t in Ioi (0 : ℝ), f ω t ∂volume) ∂P := lintegral_congr_ae hpoint
    _ = c * ∫⁻ ω, ∫⁻ t, f ω t ∂ν ∂P := lintegral_const_mul' c _ hc
    _ = c * ∫⁻ t, ∫⁻ ω, f ω t ∂P ∂ν := by
          congr 1
          exact lintegral_lintegral_swap hf
    _ = c * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(m ω * t))) ∂P) ∂volume := by
          congr 1
          apply lintegral_congr_ae
          exact hfactor

end DOZZ.Proofs
