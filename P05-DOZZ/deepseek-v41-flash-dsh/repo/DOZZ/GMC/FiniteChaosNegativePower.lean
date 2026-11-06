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

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Distributions

namespace DOZZ.Proofs

/-- Integrating the pointwise Mellin formula expresses a negative moment as a weighted integral
of Laplace transforms. Tonelli is applied on the probability space times the positive half-line. -/
theorem finite_rpow_neg_lintegral_eq_weighted_laplace
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : Ω → ℝ)
    (hm : ∀ ω, 0 < m ω) (hmA : AEMeasurable m P) (q : ℝ) (hq : 0 < q) :
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (m ω)) (-q) ∂P =
      ENNReal.ofReal (1 / Real.Gamma q) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(m ω * t))) ∂P) ∂volume := by
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let c : ℝ≥0∞ := ENNReal.ofReal (1 / Real.Gamma q)
  let f : Ω → ℝ → ℝ≥0∞ := fun ω t =>
    ENNReal.ofReal (t ^ (q - 1) * Real.exp (-(m ω * t)))
  have hf : AEMeasurable (Function.uncurry f) (P.prod ν) := by
    have htprod : AEMeasurable (fun z : Ω × ℝ => z.2) (P.prod ν) :=
      measurable_snd.aemeasurable
    have harg : AEMeasurable (fun z : Ω × ℝ => -(m z.1 * z.2)) (P.prod ν) :=
      ((hmA.comp_fst).mul htprod).neg
    have hexp : AEMeasurable (fun z : Ω × ℝ => Real.exp (-(m z.1 * z.2)))
        (P.prod ν) := Real.measurable_exp.comp_aemeasurable harg
    have hpow : Measurable (fun z : Ω × ℝ => z.2 ^ (q - 1)) := by fun_prop
    have hreal : AEMeasurable (fun z : Ω × ℝ =>
        z.2 ^ (q - 1) * Real.exp (-(m z.1 * z.2))) (P.prod ν) :=
      hpow.aemeasurable.mul hexp
    exact hreal.ennreal_ofReal
  have hfactor : ∀ᵐ t ∂ν,
      (∫⁻ ω, f ω t ∂P) = ENNReal.ofReal (t ^ (q - 1)) *
        (∫⁻ ω, ENNReal.ofReal (Real.exp (-(m ω * t))) ∂P) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [show (fun ω => f ω t) = fun ω => ENNReal.ofReal (t ^ (q - 1)) *
        ENNReal.ofReal (Real.exp (-(m ω * t))) by
          funext ω
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (ht).le _)] ]
    exact lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)
  have hpoint (ω : Ω) :
      ENNReal.rpow (ENNReal.ofReal (m ω)) (-q) =
        c * ∫⁻ t in Ioi (0 : ℝ), f ω t ∂volume := by
    change ENNReal.ofReal (m ω) ^ (-q) = _
    rw [ENNReal.ofReal_rpow_of_pos (hm ω)]
    simpa [c, f] using ofReal_rpow_neg_eq_mellin_lintegral (hm ω) hq
  calc
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (m ω)) (-q) ∂P =
        ∫⁻ ω, c * (∫⁻ t in Ioi (0 : ℝ), f ω t ∂volume) ∂P := by
          apply lintegral_congr_ae
          exact ae_of_all P hpoint
    _ = c * ∫⁻ ω, ∫⁻ t, f ω t ∂ν ∂P := lintegral_const_mul' c _ (ENNReal.ofReal_ne_top)
    _ = c * ∫⁻ t, ∫⁻ ω, f ω t ∂P ∂ν := by
          congr 1
          exact lintegral_lintegral_swap hf
    _ = c * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(m ω * t))) ∂P) ∂volume := by
          congr 1
          apply lintegral_congr_ae
          exact hfactor

end DOZZ.Proofs
