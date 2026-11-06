/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GmcReferenceMeasure
public import DOZZ.Statements.Defs.RegularizedGMC
public import DOZZ.GMC.CircleAverageGaussian
public import DOZZ.GMC.CirclePotential
public import DOZZ.GMC.FiniteChaosMean
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Prod

/-! The finite-cutoff circle chaos has the reference measure as its expected intensity. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- At every finite circle cutoff, the expected chaos mass of a measurable set equals its
reference mass. The proof is pointwise Gaussian Wick normalization followed by Tonelli. -/
theorem regularizedGMC_lintegral_eq_reference
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    Xc (hXc : IsCircleAverage P X Xc)
    γ r A (hA : MeasurableSet A) :
    ∫⁻ ω, regularizedGMC P Xc γ r ω A ∂P = gmcReferenceMeasure A := by
  classical
  let : IsProbabilityMeasure P := hX.1
  let V : ℂ → ℝ := fun x => ∫ ω, Xc ω x r ^ 2 ∂P
  let density : Ω × ℂ → ℝ≥0∞ := fun p => ENNReal.ofReal
    (Real.exp (γ * Xc p.1 p.2 r - γ ^ 2 / 2 * V p.2) *
      normPlus p.2 ^ (-4 : ℝ))
  let G : Ω × ℂ → ℝ≥0∞ := fun p => if p.2 ∈ A then density p else 0
  have hVmeas : Measurable V := by
    let q : ℂ → Ω → ℝ := fun x ω => Xc ω x r ^ 2
    have hq : Measurable (Function.uncurry q) := by
      have hbase := (hXc.1 r).comp measurable_swap
      change Measurable (fun p : ℂ × Ω => Xc p.2 p.1 r ^ 2)
      rw [(show (fun p : ℂ × Ω => Xc p.2 p.1 r ^ 2) = fun p => Xc p.2 p.1 r * Xc p.2 p.1 r by funext p; ring)]
      exact hbase.mul hbase
    change Measurable (fun x => ∫ ω, q x ω ∂P)
    exact hq.stronglyMeasurable.integral_prod_right.measurable
  have := hXc.1 r
  have : Measurable (fun p : Ω × ℂ => normPlus p.2) :=
    (show Measurable (fun x => normPlus x) by unfold normPlus; exact measurable_const.max measurable_norm).comp measurable_snd
  have : Measurable (fun p : Ω × ℂ => V p.2) := hVmeas.comp measurable_snd
  have hG : Measurable G := by
    exact Measurable.ite (hA.preimage measurable_snd) (by dsimp [density]; fun_prop) measurable_const
  have hV x : gaussianVariance P (fun ω => Xc ω x r) = V x := by
    simp [V, gaussianVariance, gaussianCovariance, pow_two]
  have hwick x :
      ∫⁻ ω, ENNReal.ofReal (Real.exp
        (γ * Xc ω x r - γ ^ 2 / 2 * V x)) ∂P = 1 := by
    let p : Fin 1 → ℂ × ℝ := fun _ => (x, r)
    let Z : Ω → Fin 1 → ℝ := fun ω i => Xc ω (p i).1 (p i).2
    have hbase := wick_exponential_lintegral_expectation P Z (by simpa [Z, p] using circleAverage_finite_family_jointly_gaussian P X hX Xc hXc p) 0 γ
    simpa [Z, p, hV x] using hbase
  have hsection ω :
      ∫⁻ x in A, density (ω, x) ∂volume = ∫⁻ x, G (ω, x) ∂volume := by
    rw [← lintegral_indicator hA]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ A <;> simp [G, hx]
  have hdensityIntegral x :
      ∫⁻ ω, density (ω, x) ∂P = ENNReal.ofReal (normPlus x ^ (-4 : ℝ)) := by
    change ∫⁻ ω, ENNReal.ofReal
      (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) * normPlus x ^ (-4 : ℝ)) ∂P = _
    calc
      ∫⁻ ω, ENNReal.ofReal
          (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) * normPlus x ^ (-4 : ℝ)) ∂P
        = ∫⁻ ω, ENNReal.ofReal (Real.exp
            (γ * Xc ω x r - γ ^ 2 / 2 * V x)) *
            ENNReal.ofReal (normPlus x ^ (-4 : ℝ)) ∂P := by
              apply lintegral_congr
              intro ω
              exact ENNReal.ofReal_mul (Real.exp_nonneg _)
      _ = (∫⁻ ω, ENNReal.ofReal (Real.exp
            (γ * Xc ω x r - γ ^ 2 / 2 * V x)) ∂P) *
            ENNReal.ofReal (normPlus x ^ (-4 : ℝ)) := by
              exact lintegral_mul_const'' _ (by fun_prop)
      _ = ENNReal.ofReal (normPlus x ^ (-4 : ℝ)) := by rw [hwick x, one_mul]
  calc
    ∫⁻ ω, regularizedGMC P Xc γ r ω A ∂P =
        ∫⁻ ω, ∫⁻ x, G (ω, x) ∂volume ∂P := by
          apply lintegral_congr
          intro ω
          rw [regularizedGMC, withDensity_apply _ hA]
          exact hsection ω
    _ = ∫⁻ x, ∫⁻ ω, G (ω, x) ∂P ∂volume := by
          rw [← lintegral_prod G hG.aemeasurable,
            lintegral_prod_symm G hG.aemeasurable]
    _ = ∫⁻ x in A, ENNReal.ofReal (normPlus x ^ (-4 : ℝ)) ∂volume := by
          rw [← lintegral_indicator hA]
          apply lintegral_congr
          intro x
          by_cases hx : x ∈ A
          · simp [G, hx, hdensityIntegral]
          · simp [G, hx]
    _ = gmcReferenceMeasure A := by
          rw [gmcReferenceMeasure, withDensity_apply _ hA]

end DOZZ.Proofs
