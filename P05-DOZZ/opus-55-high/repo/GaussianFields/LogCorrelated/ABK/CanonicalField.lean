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

section
variable {d : Nat} {normalization : ℝ} {ζ : ABKCutoff d} {ψ : MeanZeroTestFunction d}

/-- Product-coordinate `L²` membership implies concrete scale-space `L²` membership. -/
theorem memLp_abkLogKernel_of_prod (hprod :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d))) :
    MemLp (abkLogKernel normalization ζ ψ) 2
      (volume : Measure (ScaleSpace d)) := by
  simpa [abkLogKernel] using
    hprod.comp_measurePreserving (scaleSpaceMeasurePreserving d)

/-- Square-integrability of the concrete ABK product kernel is exactly the `L²` input needed by
white noise. -/
theorem memLp_abkLogKernelProd_of_integrable_sq (hmeas :
      AEStronglyMeasurable (abkLogKernelProd normalization ζ ψ)
        (volume : Measure (ℝ × Vec d)))
    (hint :
      Integrable (fun p : ℝ × Vec d =>
        (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat))
        (volume : Measure (ℝ × Vec d))) :
    MemLp (abkLogKernelProd normalization ζ ψ) 2
      (volume : Measure (ℝ × Vec d)) := by
  rwa [memLp_two_iff_integrable_sq hmeas]

end
section
variable {d : Nat}

/-- Fubini bookkeeping for product kernels on `R × R^d`: integrable sections plus an integrable
majorant for the spatial norm integrals imply product integrability. -/
theorem integrable_prod_of_integrable_norm_integral {f : ℝ × Vec d → ℝ}
    (hf :
      AEStronglyMeasurable f
        ((volume : Measure ℝ).prod (volume : Measure (Vec d))))
    (hsections :
      ∀ᵐ r ∂(volume : Measure ℝ),
        Integrable (fun y : Vec d => f (r, y)) (volume : Measure (Vec d)))
    (g : ℝ → ℝ) (hg : Integrable g (volume : Measure ℝ))
    (hscaleMeas :
      AEStronglyMeasurable
        (fun r : ℝ => ∫ y : Vec d, ‖f (r, y)‖ ∂(volume : Measure (Vec d)))
        (volume : Measure ℝ))
    (hbound :
      ∀ᵐ r ∂(volume : Measure ℝ),
        (∫ y : Vec d, ‖f (r, y)‖ ∂(volume : Measure (Vec d))) ≤ g r) :
    Integrable f ((volume : Measure ℝ).prod (volume : Measure (Vec d))) := by
  rw [integrable_prod_iff hf]
  have hbound_norm :
      ∀ᵐ r ∂(volume : Measure ℝ),
        ‖∫ y : Vec d, ‖f (r, y)‖ ∂volume‖ ≤ g r := by
    filter_upwards [hbound] with r hr
    have hnonneg : 0 ≤ ∫ y : Vec d, ‖f (r, y)‖ ∂(volume : Measure (Vec d)) :=
      integral_nonneg fun y => norm_nonneg _
    rwa [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact ⟨hsections, Integrable.mono' hg hscaleMeas hbound_norm⟩

/-- Square-integrability of the ABK product kernel follows from sectionwise square-integrability
and an integrable scale majorant for the spatial square masses. -/
theorem integrable_sq_abkLogKernelProd_of_scale_majorant {normalization : ℝ}
    {ζ : ABKCutoff d} {ψ : MeanZeroTestFunction d}
    (hmeas :
      AEStronglyMeasurable
        (fun p : ℝ × Vec d => (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat))
        ((volume : Measure ℝ).prod (volume : Measure (Vec d))))
    (hsections :
      ∀ᵐ r ∂(volume : Measure ℝ),
        Integrable
          (fun y : Vec d => (abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat))
          (volume : Measure (Vec d)))
    (g : ℝ → ℝ) (hg : Integrable g (volume : Measure ℝ))
    (hscaleMeas :
      AEStronglyMeasurable
        (fun r : ℝ =>
          ∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
            ∂(volume : Measure (Vec d)))
        (volume : Measure ℝ))
    (hbound :
      ∀ᵐ r ∂(volume : Measure ℝ),
        (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
          ∂(volume : Measure (Vec d))) ≤ g r) :
    Integrable
      (fun p : ℝ × Vec d => (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat))
      ((volume : Measure ℝ).prod (volume : Measure (Vec d))) :=
  integrable_prod_of_integrable_norm_integral hmeas hsections g hg hscaleMeas hbound

end

/-- The ABK scale majorant obtained from the squared small- and large-scale estimates:
`r^(d-1)` on `(0,1]` and `r^-3` on `(1,∞)`. -/
@[expose]
noncomputable def abkScaleMajorant (d : Nat) (C0 Cinf : ℝ) : ℝ → ℝ :=
  (Set.Ioc (0 : ℝ) 1).indicator (fun r : ℝ => C0 * r ^ ((d : ℝ) - 1)) +
    (Set.Ioi (1 : ℝ)).indicator (fun r : ℝ => Cinf * r ^ (-3 : ℝ))

/-- The scale majorant dictated by the ABK small/large estimates is integrable for positive
spatial dimension. -/
theorem integrable_abkScaleMajorant {d : Nat} (hd : 0 < d) (C0 Cinf : ℝ) :
    Integrable (abkScaleMajorant d C0 Cinf) (volume : Measure ℝ) := by
  have hd_exp : (-1 : ℝ) < (d : ℝ) - 1 := by
    simp_all
  have hsmallIoo :
      IntegrableOn (fun r => r ^ ((d : ℝ) - 1)) (Set.Ioo (0 : ℝ) 1)
        (volume : Measure ℝ) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2 hd_exp
  have hsmall :
      IntegrableOn (fun r => C0 * r ^ ((d : ℝ) - 1)) (Set.Ioc (0 : ℝ) 1)
        (volume : Measure ℝ) := by
    exact (hsmallIoo.congr_set_ae Ioo_ae_eq_Ioc.symm).const_mul C0
  have hlargePow :
      IntegrableOn (fun r => r ^ (-3 : ℝ)) (Set.Ioi (1 : ℝ))
        (volume : Measure ℝ) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 1)
  have hlarge :
      IntegrableOn (fun r => Cinf * r ^ (-3 : ℝ)) (Set.Ioi (1 : ℝ))
        (volume : Measure ℝ) := by
    exact hlargePow.const_mul Cinf
  exact (hsmall.integrable_indicator measurableSet_Ioc).add
    (hlarge.integrable_indicator measurableSet_Ioi)
section
variable {d : Nat} {normalization : ℝ} {ζ : ABKCutoff d} {ψ : MeanZeroTestFunction d} (hd : 0 < d)
include hd

/-- The ABK weighted small/large spatial square bounds imply square-integrability of the full
product kernel.  The two bounds correspond to
`r^{-(d+1)} ‖ζ_r * ψ‖_2^2 = O(r^{d-1})` as `r ↓ 0` and `O(r^-3)` as `r → ∞`. -/
theorem integrable_sq_abkLogKernelProd_of_weighted_spatial_bounds (hmeas :
      AEStronglyMeasurable
        (fun p : ℝ × Vec d => (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat))
        ((volume : Measure ℝ).prod (volume : Measure (Vec d))))
    (hsections :
      ∀ᵐ r ∂(volume : Measure ℝ),
        Integrable
          (fun y : Vec d => (abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat))
          (volume : Measure (Vec d)))
    (hscaleMeas :
      AEStronglyMeasurable
        (fun r : ℝ =>
          ∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
            ∂(volume : Measure (Vec d)))
        (volume : Measure ℝ))
    (C0 Cinf : ℝ)
    (hsmall :
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
          ∂(volume : Measure (Vec d))) ≤ C0 * r ^ ((d : ℝ) - 1))
    (hlarge :
      ∀ r : ℝ, 1 < r →
        (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
          ∂(volume : Measure (Vec d))) ≤ Cinf * r ^ (-3 : ℝ)) :
    Integrable
      (fun p : ℝ × Vec d => (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat))
      ((volume : Measure ℝ).prod (volume : Measure (Vec d))) := by
  refine integrable_sq_abkLogKernelProd_of_scale_majorant
    hmeas hsections _
    (integrable_abkScaleMajorant hd C0 Cinf) hscaleMeas ?_
  filter_upwards with r
  by_cases hrpos : 0 < r
  · by_cases hrle : r ≤ 1
    · have hsmallMem : r ∈ Set.Ioc 0 1 := ⟨hrpos, hrle⟩
      simpa [abkScaleMajorant, hsmallMem, (not_lt.mpr hrle)] using hsmall r hrpos hrle
    · have hrlarge := lt_of_not_ge hrle
      have hsmallNot : r ∉ Set.Ioc 0 1 := fun hr => hrle hr.2
      simpa [abkScaleMajorant, hsmallNot, hrlarge] using hlarge r hrlarge
  · have hrnonpos := le_of_not_gt hrpos
    have hsmallNot : r ∉ Set.Ioc 0 1 := fun hr => hrpos hr.1
    have hlargeNot : r ∉ Set.Ioi (1 : ℝ) :=
      not_lt.mpr (le_trans hrnonpos (by norm_num))
    have hzero :
        (fun y : Vec d => ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ 2‖) =
          fun _ => 0 := by
      funext y
      simp [abkLogKernelProd, hrpos]
    rw [hzero, integral_zero]
    simp [abkScaleMajorant, hsmallNot, hlargeNot]

/-- The ABK weighted spatial square bounds give the `L²` product-kernel proof needed by the
isonormal white-noise construction. -/
theorem memLp_abkLogKernelProd_of_weighted_spatial_bounds (hkernelMeas :
      AEStronglyMeasurable (abkLogKernelProd normalization ζ ψ)
        (volume : Measure (ℝ × Vec d)))
    (hsqMeas :
      AEStronglyMeasurable
        (fun p : ℝ × Vec d => (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat))
        ((volume : Measure ℝ).prod (volume : Measure (Vec d))))
    (hsections :
      ∀ᵐ r ∂(volume : Measure ℝ),
        Integrable
          (fun y : Vec d => (abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat))
          (volume : Measure (Vec d)))
    (hscaleMeas :
      AEStronglyMeasurable
        (fun r : ℝ =>
          ∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
            ∂(volume : Measure (Vec d)))
        (volume : Measure ℝ))
    (C0 Cinf : ℝ)
    (hsmall :
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
          ∂(volume : Measure (Vec d))) ≤ C0 * r ^ ((d : ℝ) - 1))
    (hlarge :
      ∀ r : ℝ, 1 < r →
        (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
          ∂(volume : Measure (Vec d))) ≤ Cinf * r ^ (-3 : ℝ)) :
    MemLp (abkLogKernelProd normalization ζ ψ) 2
      (volume : Measure (ℝ × Vec d)) := by
  refine memLp_abkLogKernelProd_of_integrable_sq hkernelMeas ?_
  exact 
    integrable_sq_abkLogKernelProd_of_weighted_spatial_bounds
     
      hd hsqMeas hsections hscaleMeas C0 Cinf hsmall hlarge

/-- The proved ABK small- and large-scale estimates put the deterministic product-coordinate
kernel in `L²`. -/
theorem memLp_abkLogKernelProd_of_abk_estimates :
    MemLp (abkLogKernelProd normalization ζ ψ) 2
      (volume : Measure (ℝ × Vec d)) := by
  rcases integral_norm_sq_abkLogKernelProd_le_small normalization ζ ψ with
    ⟨C0, _hC0_nonneg, hsmall⟩
  rcases integral_norm_sq_abkLogKernelProd_le_large normalization ζ ψ with
    ⟨Cinf, _hCinf_nonneg, hlarge⟩
  have hsections :
      ∀ᵐ r ∂(volume : Measure ℝ),
        Integrable
          (fun y => (abkLogKernelProd normalization ζ ψ _) ^ (2 : Nat))
          (volume : Measure (Vec d)) :=
    Filter.Eventually.of_forall fun r =>
      integrable_sq_abkLogKernelProd_section normalization ζ ψ r
  have hkernelMeas :=
    aestronglyMeasurable_abkLogKernelProd normalization ζ ψ volume
  have hsqMeas :=
    aestronglyMeasurable_sq_abkLogKernelProd normalization ζ ψ
      (volume.prod volume)
  have hscaleMeas :=
    aestronglyMeasurable_integral_norm_sq_abkLogKernelProd_section normalization ζ ψ
  refine memLp_abkLogKernelProd_of_weighted_spatial_bounds
   
    hd hkernelMeas hsqMeas hsections hscaleMeas C0 Cinf ?_ ?_
  · intro r hrpos hrle
    exact hsmall r hrpos hrle (integrable_sq_abkSpatialConvolution ζ ψ hrpos)
  · intro r hrlarge
    exact hlarge r (le_of_lt hrlarge)
      (integrable_sq_abkSpatialConvolution ζ ψ (lt_trans zero_lt_one hrlarge))

end

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
section
variable {d : Nat} (normalization : ℝ) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) (hψ : MemLp (abkLogKernelProd normalization ζ ψ) 2 (volume : Measure (ℝ × Vec d))) (hφ : MemLp (abkLogKernelProd normalization ζ φ) 2 (volume : Measure (ℝ × Vec d)))


/-- Covariance of ABK field evaluations is the deterministic `L²` inner product of their
scale-space kernels. -/
theorem covariance_abkLogCorrelatedFieldL2 :
    cov[abkLogCorrelatedFieldL2 normalization ζ ψ hψ,
        abkLogCorrelatedFieldL2 normalization ζ φ hφ;
        scaleSpaceWhiteNoiseMeasure d] =
      ⟪abkLogKernelLp normalization ζ ψ hψ,
        abkLogKernelLp normalization ζ φ hφ⟫_ℝ := covariance_scaleSpaceWhiteNoiseL2
    (abkLogKernelLp normalization ζ ψ hψ)
    (abkLogKernelLp normalization ζ φ hφ)

/-- The deterministic kernel inner product is represented by the integral of the product of
concrete kernels. -/
theorem inner_abkLogKernelLp_eq_integral :
    ⟪abkLogKernelLp normalization ζ ψ hψ,
        abkLogKernelLp normalization ζ φ hφ⟫_ℝ =
      ∫ z : ScaleSpace d,
        abkLogKernel normalization ζ ψ z *
          abkLogKernel normalization ζ φ z := inner_toLp_real
    (memLp_abkLogKernel_of_prod hψ)
    (memLp_abkLogKernel_of_prod hφ)

/-- Product-coordinate form of the deterministic kernel inner product. -/
theorem inner_abkLogKernelLp_eq_prod_integral :
    ⟪abkLogKernelLp normalization ζ ψ hψ,
        abkLogKernelLp normalization ζ φ hφ⟫_ℝ =
      ∫ p : ℝ × Vec d,
        abkLogKernelProd normalization ζ ψ p *
          abkLogKernelProd normalization ζ φ p := by
  rw [inner_abkLogKernelLp_eq_integral]
  exact (scaleSpaceMeasurePreserving d).integral_comp'
   
    (g := fun p =>
      abkLogKernelProd normalization ζ ψ p *
        abkLogKernelProd normalization ζ φ p)

/-- Product-coordinate covariance formula for the ABK log-correlated field. -/
theorem covariance_abkLogCorrelatedFieldL2_eq_prod_integral :
    cov[abkLogCorrelatedFieldL2 normalization ζ ψ hψ,
        abkLogCorrelatedFieldL2 normalization ζ φ hφ;
        scaleSpaceWhiteNoiseMeasure d] =
      ∫ p : ℝ × Vec d,
        abkLogKernelProd normalization ζ ψ p *
          abkLogKernelProd normalization ζ φ p := by
  rw [covariance_abkLogCorrelatedFieldL2,
    inner_abkLogKernelLp_eq_prod_integral]

end

end GaussianFields

end
