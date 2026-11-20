/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.ScaleLimit.PowerDecomposition

/-!
# GaussianFields ABK scale limit closure

Port of the corresponding GaussianFields source module.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

section
variable {d : Nat} (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)

/-- The absolute value of a fixed-scale product section is bounded by half the sum of the two
square sections. -/
theorem abs_abkScaleProductSection_le_half_sq_sections (r : ℝ) :
    |abkScaleProductSection ζ ψ φ r| ≤
      ((∫ y : Vec d, ‖(abkLogKernelProd 1 ζ ψ (r, y)) ^ (2 : Nat)‖
          ∂(volume : Measure (Vec d))) +
        ∫ y : Vec d, ‖(abkLogKernelProd 1 ζ φ (r, y)) ^ (2 : Nat)‖
          ∂(volume : Measure (Vec d))) / 2 := by
  let A  := fun y => abkLogKernelProd 1 ζ ψ (r, y)
  let B  := fun y => abkLogKernelProd 1 ζ φ (r, y)
  have hprod_int : Integrable (fun y : Vec d => A y * B y)
      (volume : Measure (Vec d)) := by
    simpa [A, B] using integrable_abkLogKernelProd_mul_section 1 ζ ψ φ r
  have hA_sq : Integrable (fun y : Vec d => (A y) ^ (2 : Nat))
      (volume : Measure (Vec d)) := by
    simpa [A] using integrable_sq_abkLogKernelProd_section 1 ζ ψ r
  have hB_sq : Integrable (fun y : Vec d => (B y) ^ (2 : Nat))
      (volume : Measure (Vec d)) := by
    simpa [B] using integrable_sq_abkLogKernelProd_section 1 ζ φ r
  have hmajor_int :
      Integrable
        (fun y : Vec d => (‖(A y) ^ (2 : Nat)‖ + ‖(B y) ^ (2 : Nat)‖) / 2)
        (volume : Measure (Vec d)) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (hA_sq.norm.add hB_sq.norm).const_mul ((2 : ℝ)⁻¹)
  have hpoint :
      (fun y : Vec d => ‖A y * B y‖) ≤ᶠ[ae (volume : Measure (Vec d))]
        fun y : Vec d => (‖(A y) ^ (2 : Nat)‖ + ‖(B y) ^ (2 : Nat)‖) / 2 := by
    filter_upwards with y
    have h := abs_mul_le_half_sq_add_sq (A y) (B y)
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (A y)),
      abs_of_nonneg (sq_nonneg (B y))] using h
  calc
    |abkScaleProductSection ζ ψ φ r|
        = ‖∫ y : Vec d, A y * B y ∂(volume : Measure (Vec d))‖ := by
          rfl
    _ ≤ ∫ y : Vec d, ‖A y * B y‖ ∂(volume : Measure (Vec d)) :=
          norm_integral_le_integral_norm (fun y : Vec d => A y * B y)
    _ ≤ ∫ y : Vec d, (‖(A y) ^ (2 : Nat)‖ + ‖(B y) ^ (2 : Nat)‖) / 2
          ∂(volume : Measure (Vec d)) :=
          integral_mono_ae hprod_int.norm hmajor_int hpoint
    _ =
        ((∫ y : Vec d, ‖(abkLogKernelProd 1 ζ ψ (r, y)) ^ (2 : Nat)‖
            ∂(volume : Measure (Vec d))) +
          ∫ y : Vec d, ‖(abkLogKernelProd 1 ζ φ (r, y)) ^ (2 : Nat)‖
            ∂(volume : Measure (Vec d))) / 2 := by
          rw [integral_div, integral_add hA_sq.norm hB_sq.norm]

/-- A common power bound on two square sections controls their mixed section. -/
private theorem abkScaleProductSection_le_of_sq_bounds (r A B w : ℝ)
    (hψ : (∫ y : Vec d, ‖(abkLogKernelProd 1 ζ ψ (r, y)) ^ (2 : Nat)‖) ≤ A * w)
    (hφ : (∫ y : Vec d, ‖(abkLogKernelProd 1 ζ φ (r, y)) ^ (2 : Nat)‖) ≤ B * w) :
    |abkScaleProductSection ζ ψ φ r| ≤ ((A + B) / 2) * w := by
  refine (abs_abkScaleProductSection_le_half_sq_sections ζ ψ φ r).trans
    ((div_le_div_of_nonneg_right (add_le_add hψ hφ) (by norm_num)).trans_eq ?_)
  ring

/-- Small- and large-scale bounds for the fixed-scale product section. -/
theorem exists_abkScaleProductSection_bounds :
    ∃ C0 Cinf, 0 ≤ C0 ∧ 0 ≤ Cinf ∧
      (∀ r : ℝ, 0 < r → r ≤ 1 →
        |abkScaleProductSection ζ ψ φ r| ≤ C0 * r ^ ((d : ℝ) - 1)) ∧
      (∀ r : ℝ, 1 ≤ r →
        |abkScaleProductSection ζ ψ φ r| ≤ Cinf * r ^ (-3 : ℝ)) := by
  obtain ⟨A0, hA0, hψ0⟩ := integral_norm_sq_abkLogKernelProd_le_small 1 ζ ψ
  obtain ⟨B0, hB0, hφ0⟩ := integral_norm_sq_abkLogKernelProd_le_small 1 ζ φ
  obtain ⟨Ai, hAi, hψi⟩ := integral_norm_sq_abkLogKernelProd_le_large 1 ζ ψ
  obtain ⟨Bi, hBi, hφi⟩ := integral_norm_sq_abkLogKernelProd_le_large 1 ζ φ
  exact ⟨(A0 + B0) / 2, (Ai + Bi) / 2, by positivity, by positivity,
    fun r hr h₁ => abkScaleProductSection_le_of_sq_bounds ζ ψ φ r _ _ _ (hψ0 r hr h₁) (hφ0 r hr h₁),
    fun r h₁ => abkScaleProductSection_le_of_sq_bounds ζ ψ φ r _ _ _ (hψi r h₁) (hφi r h₁)⟩

/-- Pointwise domination of Abel-regularized scale sections by the scale majorant. -/
theorem norm_abkRegularizedScaleProductSection_le_majorant
    {C0 Cinf α r : ℝ}
    (hsmall :
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        |abkScaleProductSection ζ ψ φ r| ≤ C0 * r ^ ((d : ℝ) - 1))
    (hlarge :
      ∀ r : ℝ, 1 ≤ r →
        |abkScaleProductSection ζ ψ φ r| ≤ Cinf * r ^ (-3 : ℝ))
    (hα_pos : 0 < α) (hα_le : α ≤ 1 / 2) :
    ‖abkRegularizedScaleProductSection ζ ψ φ α r‖ ≤
      abkScaleMajorant ((d : ℝ) - 3 / 2) C0 Cinf r := by
  by_cases hr : 0 < r
  · rw [abkRegularizedScaleProductSection, ite_eq_left hr, norm_mul,
      Real.norm_of_nonneg (Real.rpow_nonneg hr.le _), Real.norm_eq_abs]
    by_cases h₁ : r ≤ 1
    · simp [abkScaleMajorant, Set.mem_Ioc, hr, h₁, not_lt.mpr h₁]
      have hp : r ^ (-α) ≤ r ^ (-(1 / 2 : ℝ)) :=
        (Real.antitone_rpow_of_base_le_one hr h₁) (by linarith)
      refine (mul_le_mul hp (hsmall r hr h₁) (abs_nonneg _) (Real.rpow_nonneg hr.le _)).trans_eq ?_
      rw [mul_left_comm, ← Real.rpow_add hr, show -(1 / 2 : ℝ) + ((d : ℝ) - 1) = d - 3 / 2 by ring]
    · have hlt := lt_of_not_ge h₁
      simp [abkScaleMajorant, Set.mem_Ioc, h₁, hlt]
      simpa using (mul_le_mul (Real.rpow_le_one_of_one_le_of_nonpos hlt.le (by linarith))
        (hlarge r hlt.le) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  · have h₁ : ¬1 < r := not_lt.mpr ((le_of_not_gt hr).trans zero_le_one)
    simp [abkRegularizedScaleProductSection, abkScaleMajorant, Set.mem_Ioc, hr, h₁]

end

section
variable {d : Nat} (hd : 0 < d) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)
include d hd

/-- Concrete integrable majorant for the Abel-regularized scale sections. -/
theorem exists_integrable_bound_abkRegularizedScaleProductSection :
    ∃ bound : ℝ → ℝ,
      Integrable bound (volume : Measure ℝ) ∧
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        ∀ᵐ r : ℝ ∂(volume : Measure ℝ),
          ‖abkRegularizedScaleProductSection ζ ψ φ α r‖ ≤ bound r := by
  rcases exists_abkScaleProductSection_bounds ζ ψ φ with
    ⟨C0, Cinf, _, _, hsmall, hlarge⟩
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast Nat.succ_le_iff.mpr hd
  refine ⟨abkScaleMajorant ((d : ℝ) - 3 / 2) C0 Cinf,
    integrable_abkScaleMajorant (by linarith) C0 Cinf, ?_⟩
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with α hα
  exact Filter.Eventually.of_forall fun r =>
    norm_abkRegularizedScaleProductSection_le_majorant
      ζ ψ φ hsmall hlarge hα.1 hα.2

/-- Abel convergence of the scale-product integrals. -/
theorem tendsto_integral_abkRegularizedScaleProductSection :
    Tendsto
      (fun α : ℝ =>
        ∫ r : ℝ, abkRegularizedScaleProductSection ζ ψ φ α r
          ∂(volume : Measure ℝ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ r : ℝ, abkScaleProductSection ζ ψ φ r ∂(volume : Measure ℝ))) := by
  rcases exists_integrable_bound_abkRegularizedScaleProductSection hd ζ ψ φ with
    ⟨bound, hbound_int, hbound⟩
  exact tendsto_integral_filter_of_dominated_convergence
    bound
    (eventually_aestronglyMeasurable_abkRegularizedScaleProductSection ζ ψ φ)
    hbound hbound_int
    (ae_tendsto_abkRegularizedScaleProductSection ζ ψ φ)

/-- The unregularized scale-product integral is the logarithmic covariance pairing with the
`M₀` prefactor. -/
theorem integral_abkScaleProductSection_eq_m0_logCovariancePairing :
    (∫ r : ℝ, abkScaleProductSection ζ ψ φ r ∂(volume : Measure ℝ)) =
      abkM0 ζ * abkLogCovariancePairing ψ φ := by
  let f  := fun α =>
    ∫ r : ℝ, abkRegularizedScaleProductSection ζ ψ φ α r
      ∂(volume : Measure ℝ)
  have hscale := tendsto_integral_abkRegularizedScaleProductSection hd ζ ψ φ
  have hriesz := tendsto_abkMAlphaInv_mul_centeredRieszDifferencePairing hd ζ ψ φ
  have heq :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        f α =
          abkMAlphaInv ζ α * abkCenteredRieszDifferencePairing ψ φ α := by
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with α hα
    exact integral_abkRegularizedScaleProductSection_eq_mAlphaInv_mul_centeredRiesz
      hd ζ ψ φ hα.1 hα.2
  have hlog := hriesz.congr' (heq.mono fun α h => h.symm)
  exact tendsto_nhds_unique hscale hlog

/-- Final Appendix A covariance formula for the canonically normalized ABK log-correlated
Gaussian field. -/
theorem covariance_abkLogCorrelatedFieldL2Canonical_eq_logCovariancePairing :
    cov[abkLogCorrelatedFieldL2Canonical hd ζ ψ,
        abkLogCorrelatedFieldL2Canonical hd ζ φ;
        scaleSpaceWhiteNoiseMeasure d] =
      abkLGFCovarianceConstant d * abkLogCovariancePairing ψ φ := by
  rw [covariance_abkLogCorrelatedFieldL2Canonical_eq_scale_selfConvolution_integral
    hd ζ ψ φ]
  have hscale :
      (∫ r : ℝ,
          if 0 < r then
            abkNormalizationRadicand ζ * r ^ (-((d : ℝ) + 1)) *
              (∫ x : Vec d,
                ψ x *
                  (∫ z : Vec d,
                    φ z * abkScaledCutoffSelfConvolution ζ r (x - z)
                    ∂(volume : Measure (Vec d)))
                ∂(volume : Measure (Vec d)))
          else
            0
          ∂(volume : Measure ℝ)) =
        abkNormalizationRadicand ζ *
          (∫ r : ℝ, abkScaleProductSection ζ ψ φ r ∂(volume : Measure ℝ)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards with r
    by_cases hr : 0 < r
    · rw [ite_eq_left hr, abkScaleProductSection_eq_selfConvolution_integral_of_pos ζ ψ φ hr]
      ring_nf
    · rw [ite_eq_right hr, abkScaleProductSection_eq_zero_of_not_pos ζ ψ φ hr]
      ring_nf
  rw [hscale]
  rw [integral_abkScaleProductSection_eq_m0_logCovariancePairing hd ζ ψ φ]
  exact abkNormalizationRadicand_mul_logCovarianceLimit ζ ψ φ

end

end GaussianFields

end
