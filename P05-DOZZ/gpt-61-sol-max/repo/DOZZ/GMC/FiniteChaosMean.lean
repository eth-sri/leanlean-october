/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FiniteChaosMoment
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Tactic

/-! First-moment normalization for finite Wick chaos sums. -/

public section

open MeasureTheory ProbabilityTheory
open scoped Distributions NNReal

namespace DOZZ.Proofs

variable {Ω ι : Type*} [_inst1 : MeasurableSpace Ω] [_inst2 : Fintype ι] (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z)

include Ω ι _inst1 _inst2 P Z hZ
private lemma coordinate_law  (i : ι) :
    ∃ v : ℝ≥0, P.map (fun ω => Z ω i) = gaussianReal (0 : ℝ) v := by
  classical
  let e : ι → ℝ := Pi.single i (1 : ℝ)
  obtain ⟨v, hv⟩ := (hZ.2.2 e).2
  refine ⟨v, ?_⟩
  have hsum : (fun ω => ∑ j, e j * Z ω j) = fun ω => Z ω i := by
    funext ω
    simp [e, Pi.single_apply]
  simpa only [hsum] using hv


/-- A coordinate of a centered jointly Gaussian vector has the centered Gaussian law whose
variance is its covariance-form diagonal. -/
lemma coordinate_mean_variance  (i : ι) :
    ∃ v : ℝ≥0, P.map (fun ω => Z ω i) = gaussianReal (0 : ℝ) v ∧
      (∫ ω, Z ω i ∂P) = 0 ∧ gaussianVariance P (fun ω => Z ω i) = (v : ℝ) := by
  classical
  obtain ⟨v, hmap⟩ := coordinate_law P Z hZ i
  let Zi : Ω → ℝ := fun ω => Z ω i
  have hZi : AEMeasurable Zi P := hZ.2.1 i
  have hIdMap : Integrable id (P.map Zi) := by
    rw [hmap]
    exact ProbabilityTheory.IsGaussian.integrable_id
  have hmeanMap := integral_map hZi hIdMap.aestronglyMeasurable
  have hmean : (∫ ω, Zi ω ∂P) = 0 := by
    continuity
  have hvarMap  := variance_map aemeasurable_id hZi
  have hvarP : Var[Zi; P] = (v : ℝ) := by
    continuity
  have hvarEq : Var[Zi; P] = gaussianVariance P Zi := by
    rw [variance_eq_integral hZi, hmean, gaussianVariance, gaussianCovariance]
    congr 1
    funext ω
    simp [pow_two]
  grind


/-- Each coordinate Wick exponential is integrable and has expectation one. -/
theorem wick_exponential_integrable_expectation

    (i : ι) (γ : ℝ) :
    Integrable (fun ω => Real.exp (γ * Z ω i - γ ^ 2 / 2 *
      gaussianVariance P (fun ω => Z ω i))) P ∧
      (∫ ω, Real.exp (γ * Z ω i - γ ^ 2 / 2 *
        gaussianVariance P (fun ω => Z ω i)) ∂P) = 1 := by
  obtain ⟨v, hmap, _, hvar⟩ := coordinate_mean_variance P Z hZ i
  let Zi : Ω → ℝ := fun ω => Z ω i
  have hZi  := hZ.2.1 i
  have hExpMap : Integrable (fun x : ℝ => Real.exp (γ * x)) (P.map Zi) := by
    rw [hmap]
    exact integrable_exp_mul_gaussianReal γ
  have hExp : Integrable (fun ω => Real.exp (γ * Zi ω)) P := (integrable_map_measure hExpMap.aestronglyMeasurable hZi).mp hExpMap
  have hWick : Integrable
      (fun ω => Real.exp (γ * Zi ω - γ ^ 2 / 2 * gaussianVariance P Zi)) P := by
    convert hExp.const_mul (Real.exp (-(γ ^ 2 / 2 * gaussianVariance P Zi))) using 1
    ext ω
    rw [show γ * Zi ω - γ ^ 2 / 2 * gaussianVariance P Zi =
      -(γ ^ 2 / 2 * gaussianVariance P Zi) + γ * Zi ω by ring]
    rw [Real.exp_add]
  have hmgf : (∫ ω, Real.exp (γ * Zi ω) ∂P) =
      Real.exp ((v : ℝ) * γ ^ 2 / 2) := by
    calc
      ∫ ω, Real.exp (γ * Zi ω) ∂P = mgf Zi P γ := rfl
      _ = mgf id (P.map Zi) γ := (congrFun (mgf_id_map hZi) γ).symm
      _ = Real.exp ((v : ℝ) * γ ^ 2 / 2) := by
        change P.map Zi = gaussianReal (0 : ℝ) v at hmap
        rw [hmap, mgf_id_gaussianReal]
        simp
  refine ⟨hWick, ?_⟩
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

    (i : ι) (γ : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * Z ω i - γ ^ 2 / 2 *
      gaussianVariance P (fun ω => Z ω i))) ∂P = 1 := by
  have h := wick_exponential_integrable_expectation P Z hZ i γ
  rw [← ofReal_integral_eq_lintegral_ofReal h.1
    (ae_of_all _ fun ω => Real.exp_nonneg _), h.2]
  simp


/-- The normalized exponential at each coordinate has expectation one, so a finite chaos sum has
the deterministic first moment given by its total weight. -/
theorem finiteChaosMass_integral
    (a : ι → ℝ) (γ : ℝ) :
    Integrable (fun ω => finiteChaosMass P Z a γ ω) P ∧
      (∫ ω, finiteChaosMass P Z a γ ω ∂P) = ∑ i, a i := by
  classical
  let term : ι → Ω → ℝ := fun i ω => a i * Real.exp
    (γ * Z ω i - γ ^ 2 / 2 * gaussianVariance P (fun ω => Z ω i))
  have hterm : ∀ i, Integrable (term i) P := by
    intro i
    have h := (wick_exponential_integrable_expectation P Z hZ i γ).1
    exact h.const_mul (a i)
  have hsumInt : Integrable (fun ω => ∑ i, term i ω) P := by
    fun_prop (disch := positivity)
  have hmass : finiteChaosMass P Z a γ = fun ω => ∑ i, term i ω := by
    funext ω
    simp [finiteChaosMass, term]
  refine ⟨hmass ▸ hsumInt, ?_⟩
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
omit Ω ι _inst1 _inst2 P Z hZ


end DOZZ.Proofs
