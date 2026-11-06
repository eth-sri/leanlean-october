/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.Kernel

/-!
# GaussianFields ABK canonical field and covariance

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped Convolution ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

/-- The ABK deterministic kernel as a function on the concrete scale-space `R^{1+d}`. -/
@[expose]
noncomputable def abkLogKernel {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) : ScaleSpace d → ℝ :=
  abkLogKernelProd normalization ζ ψ ∘ scaleSpaceMeasurableEquiv d

@[simp]
theorem abkLogKernel_apply {d} normalization
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) z :
    abkLogKernel normalization ζ ψ z =
      abkLogKernelProd normalization ζ ψ (scaleCoord z, spaceCoord z) :=
  rfl

/-- Product-coordinate `L²` membership implies concrete scale-space `L²` membership. -/
theorem memLp_abkLogKernel_of_prod {d} {normalization}
    {ζ} {ψ}
    (hprod :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d))) :
    MemLp (abkLogKernel normalization ζ ψ) 2
      (volume : Measure (ScaleSpace d)) := by
  simpa [abkLogKernel] using
    hprod.comp_measurePreserving (scaleSpaceMeasurePreserving d)




/-- The ABK scale majorant obtained from the squared small- and large-scale estimates:
`r^(d-1)` on `(0,1]` and `r^-3` on `(1,∞)`. -/
@[expose]
noncomputable def abkScaleMajorant (d : Nat) (C0 Cinf : ℝ) : ℝ → ℝ :=
  (Set.Ioc (0 : ℝ) 1).indicator (fun r : ℝ => C0 * r ^ ((d : ℝ) - 1)) +
    (Set.Ioi (1 : ℝ)).indicator (fun r : ℝ => Cinf * r ^ (-3 : ℝ))




/-- The proved ABK small- and large-scale estimates put the deterministic product-coordinate
kernel in `L²`. -/
theorem memLp_abkLogKernelProd_of_abk_estimates {d}
    {normalization} {ζ} {ψ}
    (hd : 0 < d) :
    MemLp (abkLogKernelProd normalization ζ ψ) 2
      (volume : Measure (ℝ × Vec d)) := by
  have memLp_abkLogKernelProd_of_weighted_spatial_bounds {d : Nat} {normalization} {ζ} {ψ} (hd : 0 < d) (hkernelMeas : AEStronglyMeasurable (abkLogKernelProd normalization ζ ψ) (volume : Measure (ℝ × Vec d))) (hsqMeas : AEStronglyMeasurable (fun p : ℝ × Vec d => (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat)) ((volume : Measure ℝ).prod (volume : Measure (Vec d)))) (hsections : ∀ᵐ r ∂(volume : Measure ℝ), Integrable (fun y : Vec d => (abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)) (volume : Measure (Vec d))) (hscaleMeas : AEStronglyMeasurable (fun r : ℝ => ∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖ ∂(volume : Measure (Vec d))) (volume : Measure ℝ)) C0 Cinf (hsmall : ∀ r : ℝ, 0 < r → r ≤ 1 → (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖ ∂(volume : Measure (Vec d))) ≤ C0 * r ^ ((d : ℝ) - 1)) (hlarge : ∀ r : ℝ, 1 < r → (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖ ∂(volume : Measure (Vec d))) ≤ Cinf * r ^ (-3 : ℝ)) : MemLp (abkLogKernelProd normalization ζ ψ) 2 (volume : Measure (ℝ × Vec d)) := by
    have integrable_sq_abkLogKernelProd_of_weighted_spatial_bounds {d : Nat} {normalization} {ζ} {ψ} (hd : 0 < d) (hmeas : AEStronglyMeasurable (fun p => (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat)) ((volume : Measure ℝ).prod (volume : Measure (Vec d)))) (hsections : ∀ᵐ r ∂(volume : Measure ℝ), Integrable (fun y : Vec d => (abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)) (volume : Measure (Vec d))) (hscaleMeas : AEStronglyMeasurable (fun r : ℝ => ∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖ ∂(volume : Measure (Vec d))) (volume : Measure ℝ)) C0 Cinf (hsmall : ∀ r : ℝ, 0 < r → r ≤ 1 → (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖ ∂(volume : Measure (Vec d))) ≤ C0 * r ^ ((d : ℝ) - 1)) (hlarge : ∀ r : ℝ, 1 < r → (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖ ∂(volume : Measure (Vec d))) ≤ Cinf * r ^ (-3 : ℝ)) : Integrable (fun p : ℝ × Vec d => (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat)) ((volume : Measure ℝ).prod (volume : Measure (Vec d))) := by
      have integrable_abkScaleMajorant : Integrable (abkScaleMajorant d C0 Cinf) (volume : Measure ℝ) := by
        have hd_exp : (-1 : ℝ) < (d : ℝ) - 1 := by
          have : (0 : ℝ) < d := by exact_mod_cast hd
          linarith
        have hsmall :
            IntegrableOn (fun r => C0 * r ^ ((d : ℝ) - 1)) (Set.Ioc (0 : ℝ) 1)
              (volume : Measure ℝ) := (((intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2 hd_exp).congr_set_ae Ioo_ae_eq_Ioc.symm).const_mul C0
        have hlarge :
            IntegrableOn (fun r => Cinf * r ^ (-3 : ℝ)) (Set.Ioi (1 : ℝ))
              (volume : Measure ℝ) := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)).const_mul Cinf
        exact (hsmall.integrable_indicator measurableSet_Ioc).add
          (hlarge.integrable_indicator measurableSet_Ioi)
      have integrable_prod_of_integrable_norm_integral {d} {f : ℝ × Vec d → ℝ} (hf : AEStronglyMeasurable f ((volume : Measure ℝ).prod (volume : Measure (Vec d)))) (hsections : ∀ᵐ r ∂(volume : Measure ℝ), Integrable (fun y : Vec d => f (r, y)) (volume : Measure (Vec d))) (g : ℝ → ℝ) (hg : Integrable g (volume : Measure ℝ)) (hscaleMeas : AEStronglyMeasurable (fun r => ∫ y : Vec d, ‖f (r, y)‖ ∂(volume : Measure (Vec d))) (volume : Measure ℝ)) (hbound : ∀ᵐ r ∂(volume : Measure ℝ), (∫ y : Vec d, ‖f (r, y)‖ ∂(volume : Measure (Vec d))) ≤ g r) : Integrable f ((volume : Measure ℝ).prod (volume : Measure (Vec d))) := by
        rw [integrable_prod_iff hf]
        exact ⟨hsections, Integrable.mono' hg hscaleMeas (by filter_upwards [hbound] with r hr; rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg (f (r, y)))]; exact hr)⟩
      have integrable_sq_abkLogKernelProd_of_scale_majorant {d : Nat} {normalization} {ζ} {ψ} (hmeas : AEStronglyMeasurable (fun p => (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat)) ((volume : Measure ℝ).prod (volume : Measure (Vec d)))) (hsections : ∀ᵐ r ∂(volume : Measure ℝ), Integrable (fun y : Vec d => (abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)) (volume : Measure (Vec d))) (g : ℝ → ℝ) (hg : Integrable g (volume : Measure ℝ)) (hscaleMeas : AEStronglyMeasurable (fun r => ∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖ ∂(volume : Measure (Vec d))) (volume : Measure ℝ)) (hbound : ∀ᵐ r ∂(volume : Measure ℝ), (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖ ∂(volume : Measure (Vec d))) ≤ g r) := integrable_prod_of_integrable_norm_integral hmeas hsections g hg hscaleMeas hbound
      refine integrable_sq_abkLogKernelProd_of_scale_majorant
        hmeas hsections (abkScaleMajorant d C0 Cinf)
        (integrable_abkScaleMajorant) hscaleMeas ?_
      filter_upwards with r
      by_cases hrpos : 0 < r
      · by_cases hrle : r ≤ 1
        · have hsmallMem : r ∈ Set.Ioc (0 : ℝ) 1 := ⟨hrpos, hrle⟩
          have hlargeNot := not_lt.mpr hrle
          simpa [abkScaleMajorant, hsmallMem, hlargeNot] using hsmall r hrpos hrle
        · have hrlarge : 1 < r := lt_of_not_ge hrle
          have hsmallNot : r ∉ Set.Ioc (0 : ℝ) 1 := fun hr => hrle hr.2
          have hlargeMem := hrlarge
          simpa [abkScaleMajorant, hsmallNot, hlargeMem] using hlarge r hrlarge
      · have hrnonpos : r ≤ 0 := le_of_not_gt hrpos
        have hsmallNot : r ∉ Set.Ioc (0 : ℝ) 1 := fun hr => hrpos hr.1
        have hlargeNot := not_lt.mpr (le_trans hrnonpos (by norm_num : (0 : ℝ) ≤ 1))
        have hzero :
            (fun y => ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖) =
              fun _ => 0 := by
          funext y
          simp [abkLogKernelProd, hrpos]
        rw [hzero, integral_zero]
        simp [abkScaleMajorant, hsmallNot, hlargeNot]
    have memLp_abkLogKernelProd_of_integrable_sq {d} {normalization} {ζ} {ψ} (hmeas : AEStronglyMeasurable (abkLogKernelProd normalization ζ ψ) (volume : Measure (ℝ × Vec d))) (hint : Integrable (fun p => (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat)) (volume : Measure (ℝ × Vec d))) : MemLp (abkLogKernelProd normalization ζ ψ) 2 (volume : Measure (ℝ × Vec d)) := by
      rw [memLp_two_iff_integrable_sq hmeas]
      exact hint
    refine memLp_abkLogKernelProd_of_integrable_sq hkernelMeas ?_
    have hint :=
      integrable_sq_abkLogKernelProd_of_weighted_spatial_bounds
        (d := d) (normalization := normalization) (ζ := ζ) (ψ := ψ)
        hd hsqMeas hsections hscaleMeas C0 Cinf hsmall hlarge
    rw [← Measure.volume_eq_prod ℝ (Vec d)] at hint
    exact hint
  rcases integral_norm_sq_abkLogKernelProd_le_small normalization ζ ψ with
    ⟨C0, _hC0_nonneg, hsmall⟩
  rcases integral_norm_sq_abkLogKernelProd_le_large normalization ζ ψ with
    ⟨Cinf, _hCinf_nonneg, hlarge⟩
  refine memLp_abkLogKernelProd_of_weighted_spatial_bounds
    (d := d) (normalization := normalization) (ζ := ζ) (ψ := ψ)
    hd (aestronglyMeasurable_abkLogKernelProd normalization ζ ψ (volume : Measure (ℝ × Vec d))) (aestronglyMeasurable_sq_abkLogKernelProd normalization ζ ψ ((volume : Measure ℝ).prod (volume : Measure (Vec d)))) (Filter.Eventually.of_forall fun r => integrable_sq_abkLogKernelProd_section normalization ζ ψ r) (aestronglyMeasurable_integral_norm_sq_abkLogKernelProd_section normalization ζ ψ) C0 Cinf ?_ ?_
  · intro r hrpos hrle
    exact hsmall r hrpos hrle (integrable_sq_abkSpatialConvolution ζ ψ hrpos)
  · intro r hrlarge
    exact hlarge r (le_of_lt hrlarge)
      (integrable_sq_abkSpatialConvolution ζ ψ (lt_trans zero_lt_one hrlarge))

/-- The deterministic `L²(R^{1+d})` vector sent into white noise by ABK's formula. -/
@[expose]
noncomputable def abkLogKernelLp {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d)
    (hprod :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d))) :
    ScaleSpaceWhiteNoiseHilbert d :=
  (memLp_abkLogKernel_of_prod (normalization := normalization) (ζ := ζ) (ψ := ψ) hprod).toLp
    (abkLogKernel normalization ζ ψ)

/-- The ABK log-correlated Gaussian field evaluated at a mean-zero test function. -/
@[expose]
noncomputable def abkLogCorrelatedFieldL2 {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d)
    (hprod :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d))) :
    Lp ℝ 2 (scaleSpaceWhiteNoiseMeasure d) :=
  scaleSpaceWhiteNoiseL2 d (abkLogKernelLp normalization ζ ψ hprod)




/-- Product-coordinate covariance formula for the ABK log-correlated field. -/
theorem covariance_abkLogCorrelatedFieldL2_eq_prod_integral {d}
    normalization ζ ψ φ
    (hψ :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkLogKernelProd normalization ζ φ) 2
        (volume : Measure (ℝ × Vec d))) :
    cov[abkLogCorrelatedFieldL2 normalization ζ ψ hψ,
        abkLogCorrelatedFieldL2 normalization ζ φ hφ;
        scaleSpaceWhiteNoiseMeasure d] =
      ∫ p : ℝ × Vec d,
        abkLogKernelProd normalization ζ ψ p *
          abkLogKernelProd normalization ζ φ p := by
  have inner_abkLogKernelLp_eq_prod_integral {d} normalization ζ ψ φ (hψ : MemLp (abkLogKernelProd normalization ζ ψ) 2 (volume : Measure (ℝ × Vec d))) (hφ : MemLp (abkLogKernelProd normalization ζ φ) 2 (volume : Measure (ℝ × Vec d))) : ⟪abkLogKernelLp normalization ζ ψ hψ, abkLogKernelLp normalization ζ φ hφ⟫_ℝ = ∫ p : ℝ × Vec d, abkLogKernelProd normalization ζ ψ p * abkLogKernelProd normalization ζ φ p := by
    have inner_abkLogKernelLp_eq_integral {d} normalization ζ ψ φ (hψ : MemLp (abkLogKernelProd normalization ζ ψ) 2 (volume : Measure (ℝ × Vec d))) (hφ : MemLp (abkLogKernelProd normalization ζ φ) 2 (volume : Measure (ℝ × Vec d))) : ⟪abkLogKernelLp normalization ζ ψ hψ, abkLogKernelLp normalization ζ φ hφ⟫_ℝ = ∫ z : ScaleSpace d, abkLogKernel normalization ζ ψ z * abkLogKernel normalization ζ φ z := inner_toLp_real
        (memLp_abkLogKernel_of_prod (normalization := normalization) (ζ := ζ) (ψ := ψ) hψ)
        (memLp_abkLogKernel_of_prod (normalization := normalization) (ζ := ζ) (ψ := φ) hφ)
    rw [inner_abkLogKernelLp_eq_integral]
    exact (scaleSpaceMeasurePreserving d).integral_comp'
      (f := scaleSpaceMeasurableEquiv d)
      (g := fun p =>
        abkLogKernelProd normalization ζ ψ p *
          abkLogKernelProd normalization ζ φ p)
  have covariance_abkLogCorrelatedFieldL2 {d} normalization ζ ψ φ (hψ : MemLp (abkLogKernelProd normalization ζ ψ) 2 (volume : Measure (ℝ × Vec d))) (hφ : MemLp (abkLogKernelProd normalization ζ φ) 2 (volume : Measure (ℝ × Vec d))) : cov[abkLogCorrelatedFieldL2 normalization ζ ψ hψ, abkLogCorrelatedFieldL2 normalization ζ φ hφ; scaleSpaceWhiteNoiseMeasure d] = ⟪abkLogKernelLp normalization ζ ψ hψ, abkLogKernelLp normalization ζ φ hφ⟫_ℝ := covariance_scaleSpaceWhiteNoiseL2
      (abkLogKernelLp normalization ζ ψ hψ)
      (abkLogKernelLp normalization ζ φ hφ)
  rw [covariance_abkLogCorrelatedFieldL2,
    inner_abkLogKernelLp_eq_prod_integral]

end GaussianFields

end
