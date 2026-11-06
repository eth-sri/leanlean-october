/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldGaussianCommonScalar
public import DOZZ.GMC.FieldChaosMultiNegativePower

/-! Exact common Gaussian factors for products of retained masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs



/-- A common independent Gaussian factors a product of arbitrary retained masses. This
identity preserves all cross terms between the scalar loadings. -/
theorem retained_masses_common_scalar_factor
    {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : κ → Ω → ℝ≥0∞) (hF : ∀ k, AEMeasurable (F k) P)
    (hfin : ∀ k, ∀ᵐ ω ∂P, F k ω ≠ ⊤) γ (c p : κ → ℝ) :
    (∫⁻ w : Ω × ℝ, ∏ k,
      (ENNReal.ofReal (Real.exp (γ * c k * w.2 - γ ^ 2 * c k ^ 2 / 2)) * F k w.1) ^ p k
      ∂P.prod (gaussianReal 0 1)) =
      ENNReal.ofReal (Real.exp (γ ^ 2 / 2 *
        ((∑ k, p k * c k) ^ 2 - ∑ k, p k * c k ^ 2))) *
          ∫⁻ ω, ∏ k, F k ω ^ p k ∂P := by
  classical
  have wick_scalar_product γ z (c : κ → ℝ) (p : κ → ℝ) : (∏ k, (ENNReal.ofReal (Real.exp (γ * c k * z - γ ^ 2 * c k ^ 2 / 2))) ^ p k) = ENNReal.ofReal (Real.exp (γ * (∑ k, p k * c k) * z - γ ^ 2 / 2 * ∑ k, p k * c k ^ 2)) := by
    classical
    simp_rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), Real.rpow_def_of_pos (Real.exp_pos _),
      Real.log_exp]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), ← Real.exp_sum]
    congr 2
    calc
      (∑ k, (γ * c k * z - γ ^ 2 * c k ^ 2 / 2) * p k) =
          ∑ k, ((γ * z) * (p k * c k) - (γ ^ 2 / 2) * (p k * c k ^ 2)) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
  have lintegral_gaussian_exp a b : (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (a * z - b)) ∂gaussianReal 0 1) = ENNReal.ofReal (Real.exp (a ^ 2 / 2 - b)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (show Integrable (fun z => Real.exp (a * z - b)) (gaussianReal 0 1) by simp_rw [sub_eq_add_neg, Real.exp_add]; exact (integrable_exp_mul_gaussianReal a).mul_const _)
      (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    have he : (fun z => Real.exp (a * z - b)) =
        fun z => Real.exp (-b) * Real.exp (a * z) := by
      funext z
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he, integral_const_mul]
    have hm : (∫ z : ℝ, Real.exp (a * z) ∂gaussianReal 0 1) = Real.exp (a ^ 2 / 2) := by
      change mgf id (gaussianReal 0 1) a = _
      rw [mgf_id_gaussianReal]
      simp only [zero_mul, NNReal.coe_one, one_mul, zero_add]
    rw [hm, ← Real.exp_add]
    congr 2
    ring
  let A : Ω → ℝ≥0∞ := fun ω => ∏ k, F k ω ^ p k
  let W : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp
    (γ * (∑ k, p k * c k) * z - γ ^ 2 / 2 * ∑ k, p k * c k ^ 2))
  have he : ∀ᵐ w ∂P.prod (gaussianReal 0 1),
      (∏ k, (ENNReal.ofReal (Real.exp (γ * c k * w.2 - γ ^ 2 * c k ^ 2 / 2)) *
        F k w.1) ^ p k) = A w.1 * W w.2 := by
    filter_upwards [((measurePreserving_fst (μ := P) (ν := gaussianReal 0 1)).quasiMeasurePreserving.ae (ae_all_iff.mpr hfin))] with w hw
    simp_rw [ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top (hw _)]
    rw [Finset.prod_mul_distrib, wick_scalar_product]
    exact mul_comm _ _
  rw [lintegral_congr_ae he, lintegral_prod_mul (show AEMeasurable A P by exact Finset.aemeasurable_fun_prod Finset.univ (fun k _ => (hF k).pow_const (p k))) (show Measurable W by dsimp [W]; fun_prop).aemeasurable]
  dsimp only [W]
  rw [lintegral_gaussian_exp, (show (γ * (∑ k, p k * c k)) ^ 2 / 2 - γ ^ 2 / 2 * (∑ k, p k * c k ^ 2) = γ ^ 2 / 2 * ((∑ k, p k * c k) ^ 2 - ∑ k, p k * c k ^ 2) by ring)]
  exact mul_comm _ _

end DOZZ.Proofs
