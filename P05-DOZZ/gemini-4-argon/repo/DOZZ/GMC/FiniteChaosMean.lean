/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FiniteChaosMoment
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-! First-moment normalization for finite Wick chaos sums. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions NNReal

namespace DOZZ.Proofs


/-- A coordinate of a centered jointly Gaussian vector has the centered Gaussian law whose
variance is its covariance-form diagonal. -/
lemma coordinate_mean_variance {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z) (i : ι) :
    ∃ v : ℝ≥0, P.map (fun ω => Z ω i) = gaussianReal (0 : ℝ) v ∧
      (∫ ω, Z ω i ∂P) = 0 ∧ gaussianVariance P (fun ω => Z ω i) = (v : ℝ) := by
  classical
  have coordinate_law : ∃ v : ℝ≥0, P.map (fun ω => Z ω i) = gaussianReal (0 : ℝ) v := by
    classical
    let e : ι → ℝ := Pi.single i (1 : ℝ)
    obtain ⟨v, hv⟩ := (hZ.2.2 e).2
    refine ⟨v, ?_⟩
    simpa only [(show (fun ω => ∑ j, e j * Z ω j) = fun ω => Z ω i by funext ω; simp [e, Pi.single_apply])] using hv
  obtain ⟨v, hmap⟩ := coordinate_law
  let Zi : Ω → ℝ := fun ω => Z ω i
  have hZi : AEMeasurable Zi P := hZ.2.1 i
  have hmean : (∫ ω, Zi ω ∂P) = 0 := by
    calc
      ∫ ω, Zi ω ∂P = ∫ x, x ∂P.map Zi := (integral_map hZi (show Integrable id (P.map Zi) by rw [hmap]; exact ProbabilityTheory.IsGaussian.integrable_id).aestronglyMeasurable).symm
      _ = 0 := by rw [hmap, integral_id_gaussianReal]
  have hvarMap : Var[id; P.map Zi] = Var[Zi; P] := by
    simpa only [Function.comp_def, id_def] using
      (variance_map (X := id) (Y := Zi) (μ := P)
        (aemeasurable_id) hZi)
  have hvarEq : Var[Zi; P] = gaussianVariance P Zi := by
    rw [variance_eq_integral hZi, hmean, gaussianVariance, gaussianCovariance]
    congr 1
    funext ω
    simp [pow_two]
  exact ⟨v, hmap, hmean, hvarEq.symm.trans (by change P.map Zi = gaussianReal (0 : ℝ) v at hmap; rw [hmap, variance_id_gaussianReal] at hvarMap; exact hvarMap.symm)⟩

/-- Each coordinate Wick exponential is integrable and has expectation one. -/
theorem wick_exponential_integrable_expectation
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z)
    (i : ι) (γ : ℝ) :
    Integrable (fun ω => Real.exp (γ * Z ω i - γ ^ 2 / 2 *
      gaussianVariance P (fun ω => Z ω i))) P ∧
      (∫ ω, Real.exp (γ * Z ω i - γ ^ 2 / 2 *
        gaussianVariance P (fun ω => Z ω i)) ∂P) = 1 := by
  obtain ⟨v, hmap, _, hvar⟩ := coordinate_mean_variance P Z hZ i
  let Zi : Ω → ℝ := fun ω => Z ω i
  have hZi := hZ.2.1 i
  have hExpMap : Integrable (fun x : ℝ => Real.exp (γ * x)) (P.map Zi) := by
    rw [hmap]
    exact integrable_exp_mul_gaussianReal γ
  have hmgf : (∫ ω, Real.exp (γ * Zi ω) ∂P) =
      Real.exp ((v : ℝ) * γ ^ 2 / 2) := by
    calc
      ∫ ω, Real.exp (γ * Zi ω) ∂P = mgf Zi P γ := rfl
      _ = mgf id (P.map Zi) γ := (congrFun (mgf_id_map hZi) γ).symm
      _ = Real.exp ((v : ℝ) * γ ^ 2 / 2) := by
        change P.map Zi = gaussianReal (0 : ℝ) v at hmap
        rw [hmap, mgf_id_gaussianReal]
        simp
  refine ⟨(by convert (show Integrable (fun ω => Real.exp (γ * Zi ω)) P by simpa only [Function.comp_def] using (integrable_map_measure hExpMap.aestronglyMeasurable hZi).mp hExpMap).const_mul (Real.exp (-(γ ^ 2 / 2 * gaussianVariance P Zi))) using 1; ext ω; rw [show γ * Zi ω - γ ^ 2 / 2 * gaussianVariance P Zi = -(γ ^ 2 / 2 * gaussianVariance P Zi) + γ * Zi ω by ring]; rw [Real.exp_add]), ?_⟩
  calc
    ∫ ω, Real.exp (γ * Zi ω - γ ^ 2 / 2 * gaussianVariance P Zi) ∂P
        = ∫ ω, Real.exp (γ * Zi ω) *
            Real.exp (-(γ ^ 2 / 2 * gaussianVariance P Zi)) ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          rw [show γ * Zi ω - γ ^ 2 / 2 * gaussianVariance P Zi =
            -(γ ^ 2 / 2 * gaussianVariance P Zi) + γ * Zi ω by ring]
          rw [← Real.exp_add]
          congr 1
          ring
    _ = (∫ ω, Real.exp (γ * Zi ω) ∂P) *
          Real.exp (-(γ ^ 2 / 2 * gaussianVariance P Zi)) := integral_mul_const _ _
    _ = Real.exp ((v : ℝ) * γ ^ 2 / 2 - γ ^ 2 / 2 * (v : ℝ)) := by
          rw [hmgf, hvar, ← Real.exp_add]
          exact congrArg Real.exp (by ring)
    _ = 1 := by rw [show (v : ℝ) * γ ^ 2 / 2 - γ ^ 2 / 2 * (v : ℝ) = 0 by ring,
      Real.exp_zero]

/-- The normalized exponential also has extended expectation one. This is the pointwise
Tonelli input for the intensity of a finite-cutoff chaos measure. -/
theorem wick_exponential_lintegral_expectation
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z)
    (i : ι) (γ : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * Z ω i - γ ^ 2 / 2 *
      gaussianVariance P (fun ω => Z ω i))) ∂P = 1 := by
  have h := wick_exponential_integrable_expectation P Z hZ i γ
  rw [← ofReal_integral_eq_lintegral_ofReal h.1
    (ae_of_all _ fun ω => Real.exp_nonneg _), h.2]
  simp

/-- The normalized exponential at each coordinate has expectation one, so a finite chaos sum has
the deterministic first moment given by its total weight. -/
theorem finiteChaosMass_integral {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z)
    (a : ι → ℝ) (γ : ℝ) :
    Integrable (fun ω => finiteChaosMass P Z a γ ω) P ∧
      (∫ ω, finiteChaosMass P Z a γ ω ∂P) = ∑ i, a i := by
  classical
  let term : ι → Ω → ℝ := fun i ω => a i * Real.exp
    (γ * Z ω i - γ ^ 2 / 2 * gaussianVariance P (fun ω => Z ω i))
  have hterm : ∀ i, Integrable (term i) P := by
    intro i
    exact ((wick_exponential_integrable_expectation P Z hZ i γ).1).const_mul (a i)
  have hmass : finiteChaosMass P Z a γ = fun ω => ∑ i, term i ω := by
    funext ω
    simp [finiteChaosMass, term]
  refine ⟨hmass ▸ (by exact integrable_finsetSum Finset.univ fun i hi => hterm i), ?_⟩
  rw [hmass, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [show term i = fun ω => a i * Real.exp
      (γ * Z ω i - γ ^ 2 / 2 * gaussianVariance P (fun ω => Z ω i)) from rfl,
      integral_const_mul]
    rw [(wick_exponential_integrable_expectation P Z hZ i γ).2]
    simp
  · intro i hi
    exact hterm i

end DOZZ.Proofs
