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

/-- The absolute value of a fixed-scale product section is bounded by half the sum of the two
square sections. -/
theorem abs_abkScaleProductSection_le_half_sq_sections {d}
    ζ ψ φ r :
    |abkScaleProductSection ζ ψ φ r| ≤
      ((∫ y : Vec d, ‖(abkLogKernelProd 1 ζ ψ (r, y)) ^ (2 : Nat)‖
          ∂(volume : Measure (Vec d))) +
        ∫ y : Vec d, ‖(abkLogKernelProd 1 ζ φ (r, y)) ^ (2 : Nat)‖
          ∂(volume : Measure (Vec d))) / 2 := by
  let A : Vec d → ℝ := fun y => abkLogKernelProd 1 ζ ψ (r, y)
  let B : Vec d → ℝ := fun y => abkLogKernelProd 1 ζ φ (r, y)
  have hA_sq : Integrable (fun y => (A y) ^ (2 : Nat))
      (volume : Measure (Vec d)) := by
    simpa [A] using integrable_sq_abkLogKernelProd_section 1 ζ ψ r
  have hB_sq : Integrable (fun y => (B y) ^ (2 : Nat))
      (volume : Measure (Vec d)) := by
    simpa [B] using integrable_sq_abkLogKernelProd_section 1 ζ φ r
  calc
    |abkScaleProductSection ζ ψ φ r|
        = ‖∫ y : Vec d, A y * B y ∂(volume : Measure (Vec d))‖ := by
          rw [Real.norm_eq_abs]
          rfl
    _ ≤ ∫ y : Vec d, ‖A y * B y‖ ∂(volume : Measure (Vec d)) :=
          norm_integral_le_integral_norm (fun y : Vec d => A y * B y)
    _ ≤ ∫ y : Vec d, (‖(A y) ^ (2 : Nat)‖ + ‖(B y) ^ (2 : Nat)‖) / 2
          ∂(volume : Measure (Vec d)) :=
          integral_mono_ae (show Integrable (fun y => A y * B y) (volume : Measure (Vec d)) by simpa [A, B] using integrable_abkLogKernelProd_mul_section 1 ζ ψ φ r).norm (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using (hA_sq.norm.add hB_sq.norm).const_mul ((2 : ℝ)⁻¹)) (by filter_upwards with y; simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (A y)), abs_of_nonneg (sq_nonneg (B y))] using (abs_mul_le_half_sq_add_sq (A y) (B y)))
    _ =
        ((∫ y : Vec d, ‖(abkLogKernelProd 1 ζ ψ (r, y)) ^ (2 : Nat)‖
            ∂(volume : Measure (Vec d))) +
          ∫ y : Vec d, ‖(abkLogKernelProd 1 ζ φ (r, y)) ^ (2 : Nat)‖
            ∂(volume : Measure (Vec d))) / 2 := by
          rw [integral_div, integral_add hA_sq.norm hB_sq.norm]


/-- Scale majorant for Abel regularization: an extra `r^{-1/2}` is reserved near zero. -/
@[expose]
noncomputable def abkRegularizedScaleMajorant (d : Nat) (C0 Cinf : ℝ) : ℝ → ℝ :=
  (Set.Ioc (0 : ℝ) 1).indicator (fun r : ℝ => C0 * r ^ ((d : ℝ) - 3 / 2)) +
    (Set.Ioi (1 : ℝ)).indicator (fun r : ℝ => Cinf * r ^ (-3 : ℝ))






/-- Final Appendix A covariance formula for the canonically normalized ABK log-correlated
Gaussian field. -/
theorem covariance_abkLogCorrelatedFieldL2Canonical_eq_logCovariancePairing {d}
    (hd : 0 < d) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) :
    cov[abkLogCorrelatedFieldL2Canonical hd ζ ψ,
        abkLogCorrelatedFieldL2Canonical hd ζ φ;
        scaleSpaceWhiteNoiseMeasure d] =
      abkLGFCovarianceConstant d * abkLogCovariancePairing ψ φ := by
  have integral_abkScaleProductSection_eq_m0_logCovariancePairing : (∫ r : ℝ, abkScaleProductSection ζ ψ φ r ∂(volume : Measure ℝ)) = abkM0 ζ * abkLogCovariancePairing ψ φ := by
    have tendsto_integral_abkRegularizedScaleProductSection : Tendsto (fun α : ℝ => ∫ r : ℝ, abkRegularizedScaleProductSection ζ ψ φ α r ∂(volume : Measure ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (∫ r : ℝ, abkScaleProductSection ζ ψ φ r ∂(volume : Measure ℝ))) := by
      have exists_integrable_bound_abkRegularizedScaleProductSection : ∃ bound : ℝ → ℝ, Integrable bound (volume : Measure ℝ) ∧ ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), ∀ᵐ r : ℝ ∂(volume : Measure ℝ), ‖abkRegularizedScaleProductSection ζ ψ φ α r‖ ≤ bound r := by
        have norm_abkRegularizedScaleProductSection_le_majorant {d : Nat} (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (φ : MeanZeroTestFunction d) {C0 : ℝ} {Cinf : ℝ} {α : ℝ} {r : ℝ} (hC0_nonneg : 0 ≤ C0) (hsmall : ∀ r : ℝ, 0 < r → r ≤ 1 → |abkScaleProductSection ζ ψ φ r| ≤ C0 * r ^ ((d : ℝ) - 1)) (hlarge : ∀ r : ℝ, 1 ≤ r → |abkScaleProductSection ζ ψ φ r| ≤ Cinf * r ^ (-3 : ℝ)) (hα_pos : 0 < α) (hα_le : α ≤ 1 / 2) : ‖abkRegularizedScaleProductSection ζ ψ φ α r‖ ≤ abkRegularizedScaleMajorant d C0 Cinf r := by
          by_cases hrpos : 0 < r
          · have hrpow_nonneg : 0 ≤ r ^ (-α) := Real.rpow_nonneg hrpos.le _
            by_cases hrle : r ≤ 1
            · have hsmallMem : r ∈ Set.Ioc (0 : ℝ) 1 := ⟨hrpos, hrle⟩
              calc
                ‖abkRegularizedScaleProductSection ζ ψ φ α r‖
                    = r ^ (-α) * |abkScaleProductSection ζ ψ φ r| := by
                      rw [abkRegularizedScaleProductSection, ite_eq_left hrpos,
                        Real.norm_eq_abs, abs_mul, abs_of_nonneg hrpow_nonneg]
                _ ≤ r ^ (-α) * (C0 * r ^ ((d : ℝ) - 1)) := by
                      exact mul_le_mul_of_nonneg_left (hsmall r hrpos hrle) hrpow_nonneg
                _ ≤ r ^ (-(1 / 2 : ℝ)) * (C0 * r ^ ((d : ℝ) - 1)) := by
                      exact mul_le_mul_of_nonneg_right ((Real.antitone_rpow_of_base_le_one hrpos hrle) (by linarith))
                        (mul_nonneg hC0_nonneg (Real.rpow_nonneg hrpos.le _))
                _ = C0 * r ^ ((d : ℝ) - 3 / 2) := by
                      calc
                        r ^ (-(1 / 2 : ℝ)) * (C0 * r ^ ((d : ℝ) - 1))
                            = C0 * (r ^ (-(1 / 2 : ℝ)) * r ^ ((d : ℝ) - 1)) := by
                              ring_nf
                        _ = C0 * r ^ (-(1 / 2 : ℝ) + ((d : ℝ) - 1)) := by
                              rw [Real.rpow_add hrpos]
                        _ = C0 * r ^ ((d : ℝ) - 3 / 2) := by
                              congr 1
                              ring_nf
                _ = abkRegularizedScaleMajorant d C0 Cinf r := by
                      simp [abkRegularizedScaleMajorant, hsmallMem, (not_lt.mpr hrle)]
            · have hrlarge : 1 < r := lt_of_not_ge hrle
              calc
                ‖abkRegularizedScaleProductSection ζ ψ φ α r‖
                    = r ^ (-α) * |abkScaleProductSection ζ ψ φ r| := by
                      rw [abkRegularizedScaleProductSection, ite_eq_left hrpos,
                        Real.norm_eq_abs, abs_mul, abs_of_nonneg hrpow_nonneg]
                _ ≤ 1 * (Cinf * r ^ (-3 : ℝ)) := by
                      exact mul_le_mul (Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hrlarge) (neg_nonpos.mpr hα_pos.le)) (hlarge r (le_of_lt hrlarge)) (abs_nonneg _) zero_le_one
                _ = Cinf * r ^ (-3 : ℝ) := by ring_nf
                _ = abkRegularizedScaleMajorant d C0 Cinf r := by
                      simp [abkRegularizedScaleMajorant, (fun hr => hrle hr.2 : r ∉ Set.Ioc (0 : ℝ) 1), hrlarge]
          · have hrnonpos : r ≤ 0 := le_of_not_gt hrpos
            simp [abkRegularizedScaleProductSection, hrpos, abkRegularizedScaleMajorant,
              (fun hr => hrpos hr.1 : r ∉ Set.Ioc (0 : ℝ) 1), (not_lt.mpr (le_trans hrnonpos (by norm_num : (0 : ℝ) ≤ 1)))]
        have integrable_abkRegularizedScaleMajorant C0 Cinf : Integrable (abkRegularizedScaleMajorant d C0 Cinf) (volume : Measure ℝ) := by
          have : (1 : ℝ) ≤ d := by
            exact_mod_cast (Nat.succ_le_iff.mpr hd : 1 ≤ d)
          have hsmall :
              IntegrableOn (fun r => C0 * r ^ ((d : ℝ) - 3 / 2)) (Set.Ioc (0 : ℝ) 1)
                (volume : Measure ℝ) := (((intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2 (by linarith)).congr_set_ae Ioo_ae_eq_Ioc.symm).const_mul C0
          have hlarge :
              IntegrableOn (fun r => Cinf * r ^ (-3 : ℝ)) (Set.Ioi (1 : ℝ))
                (volume : Measure ℝ) := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)).const_mul Cinf
          exact (hsmall.integrable_indicator measurableSet_Ioc).add
            (hlarge.integrable_indicator measurableSet_Ioi)
        have exists_abkScaleProductSection_bounds : ∃ C0 Cinf, 0 ≤ C0 ∧ 0 ≤ Cinf ∧ (∀ r : ℝ, 0 < r → r ≤ 1 → |abkScaleProductSection ζ ψ φ r| ≤ C0 * r ^ ((d : ℝ) - 1)) ∧ (∀ r : ℝ, 1 ≤ r → |abkScaleProductSection ζ ψ φ r| ≤ Cinf * r ^ (-3 : ℝ)) := by
          rcases integral_norm_sq_abkLogKernelProd_le_small 1 ζ ψ with
            ⟨Cψ0, hCψ0_nonneg, hψsmall⟩
          rcases integral_norm_sq_abkLogKernelProd_le_small 1 ζ φ with
            ⟨Cφ0, hCφ0_nonneg, hφsmall⟩
          rcases integral_norm_sq_abkLogKernelProd_le_large 1 ζ ψ with
            ⟨Cψinf, hCψinf_nonneg, hψlarge⟩
          rcases integral_norm_sq_abkLogKernelProd_le_large 1 ζ φ with
            ⟨Cφinf, hCφinf_nonneg, hφlarge⟩
          let C0 := (Cψ0 + Cφ0) / 2
          let Cinf := (Cψinf + Cφinf) / 2
          refine ⟨C0, Cinf, by positivity, by positivity, ?_, ?_⟩
          · intro r hr_pos hr_le_one
            calc
              |abkScaleProductSection ζ ψ φ r|
                  ≤ ((∫ y : Vec d, ‖(abkLogKernelProd 1 ζ ψ (r, y)) ^ (2 : Nat)‖
                      ∂(volume : Measure (Vec d))) +
                    ∫ y : Vec d, ‖(abkLogKernelProd 1 ζ φ (r, y)) ^ (2 : Nat)‖
                      ∂(volume : Measure (Vec d))) / 2 := (abs_abkScaleProductSection_le_half_sq_sections ζ ψ φ r)
              _ ≤ (Cψ0 * r ^ ((d : ℝ) - 1) + Cφ0 * r ^ ((d : ℝ) - 1)) / 2 := by
                    exact div_le_div_of_nonneg_right (add_le_add (hψsmall r hr_pos hr_le_one (integrable_sq_abkSpatialConvolution ζ ψ hr_pos)) (hφsmall r hr_pos hr_le_one (integrable_sq_abkSpatialConvolution ζ φ hr_pos))) (by norm_num)
              _ = C0 * r ^ ((d : ℝ) - 1) := by
                    dsimp [C0]
                    ring_nf
          · intro r hr_one
            calc
              |abkScaleProductSection ζ ψ φ r|
                  ≤ ((∫ y : Vec d, ‖(abkLogKernelProd 1 ζ ψ (r, y)) ^ (2 : Nat)‖
                      ∂(volume : Measure (Vec d))) +
                    ∫ y : Vec d, ‖(abkLogKernelProd 1 ζ φ (r, y)) ^ (2 : Nat)‖
                      ∂(volume : Measure (Vec d))) / 2 := (abs_abkScaleProductSection_le_half_sq_sections ζ ψ φ r)
              _ ≤ (Cψinf * r ^ (-3 : ℝ) + Cφinf * r ^ (-3 : ℝ)) / 2 := by
                    exact div_le_div_of_nonneg_right (add_le_add (hψlarge r hr_one (integrable_sq_abkSpatialConvolution ζ ψ (lt_of_lt_of_le zero_lt_one hr_one))) (hφlarge r hr_one (integrable_sq_abkSpatialConvolution ζ φ (lt_of_lt_of_le zero_lt_one hr_one)))) (by norm_num)
              _ = Cinf * r ^ (-3 : ℝ) := by
                    dsimp [Cinf]
                    ring_nf
        rcases exists_abkScaleProductSection_bounds with
          ⟨C0, Cinf, hC0_nonneg, _hCinf_nonneg, hsmall, hlarge⟩
        refine ⟨abkRegularizedScaleMajorant d C0 Cinf,
          integrable_abkRegularizedScaleMajorant C0 Cinf, ?_⟩
        filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with α hα
        exact Filter.Eventually.of_forall fun r =>
          norm_abkRegularizedScaleProductSection_le_majorant
            ζ ψ φ hC0_nonneg hsmall hlarge hα.1 hα.2
      rcases exists_integrable_bound_abkRegularizedScaleProductSection with
        ⟨bound, hbound_int, hbound⟩
      exact tendsto_integral_filter_of_dominated_convergence
        bound
        (eventually_aestronglyMeasurable_abkRegularizedScaleProductSection ζ ψ φ)
        hbound hbound_int
        (ae_tendsto_abkRegularizedScaleProductSection ζ ψ φ)
    exact tendsto_nhds_unique (tendsto_integral_abkRegularizedScaleProductSection) ((tendsto_abkMAlphaInv_mul_centeredRieszDifferencePairing hd ζ ψ φ).congr' ((show ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), (fun α => ∫ r : ℝ, abkRegularizedScaleProductSection ζ ψ φ α r ∂(volume : Measure ℝ)) α = abkMAlphaInv ζ α * abkCenteredRieszDifferencePairing ψ φ α by filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with α hα; exact integral_abkRegularizedScaleProductSection_eq_mAlphaInv_mul_centeredRiesz hd ζ ψ φ hα.1 hα.2).mono fun α h => h.symm))
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
  rw [hscale, integral_abkScaleProductSection_eq_m0_logCovariancePairing]
  exact abkNormalizationRadicand_mul_logCovarianceLimit ζ ψ φ

end GaussianFields

end
