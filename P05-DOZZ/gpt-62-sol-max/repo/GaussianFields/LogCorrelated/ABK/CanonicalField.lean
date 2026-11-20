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

/-- Product-coordinate `L²` membership implies concrete scale-space `L²` membership. -/
theorem memLp_abkLogKernel_of_prod {d : Nat} {normalization : ℝ}
    {ζ : ABKCutoff d} {ψ : MeanZeroTestFunction d}
    (hprod :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d))) :
    MemLp (abkLogKernel normalization ζ ψ) 2
      (volume : Measure (ScaleSpace d)) := by
  simpa [abkLogKernel] using
    hprod.comp_measurePreserving (scaleSpaceMeasurePreserving d)

/-- Scale majorant with a power `a` near zero and cubic decay at infinity. -/
@[expose]
noncomputable def abkScaleMajorant (a C0 Cinf : ℝ) : ℝ → ℝ :=
  (Set.Ioc (0 : ℝ) 1).indicator (fun r => C0 * r ^ a) +
    (Set.Ioi (1 : ℝ)).indicator (fun r => Cinf * r ^ (-3 : ℝ))

theorem integrable_abkScaleMajorant {a : ℝ} (ha : -1 < a) (C0 Cinf : ℝ) :
    Integrable (abkScaleMajorant a C0 Cinf) := by
  have hsmall := (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2 ha
  have hlarge := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 1)
  have hsmall' : IntegrableOn (fun r : ℝ => C0 * r ^ a) (Set.Ioc 0 1) :=
    (hsmall.congr_set_ae Ioo_ae_eq_Ioc.symm).const_mul C0
  have hlarge' : IntegrableOn (fun r : ℝ => Cinf * r ^ (-3 : ℝ)) (Set.Ioi 1) := hlarge.const_mul Cinf
  exact (hsmall'.integrable_indicator measurableSet_Ioc).add
    (hlarge'.integrable_indicator measurableSet_Ioi)

/-- The proved ABK small- and large-scale estimates put the deterministic product-coordinate
kernel in `L²`. -/
theorem memLp_abkLogKernelProd_of_abk_estimates {d : Nat}
    {normalization : ℝ} {ζ : ABKCutoff d} {ψ : MeanZeroTestFunction d}
    (hd : 0 < d) :
    MemLp (abkLogKernelProd normalization ζ ψ) 2
      (volume : Measure (ℝ × Vec d)) := by
  obtain ⟨C0, _, hsmall⟩ := integral_norm_sq_abkLogKernelProd_le_small normalization ζ ψ
  obtain ⟨Cinf, _, hlarge⟩ := integral_norm_sq_abkLogKernelProd_le_large normalization ζ ψ
  have hsq := aestronglyMeasurable_sq_abkLogKernelProd normalization ζ ψ
    ((volume : Measure ℝ).prod (volume : Measure (Vec d)))
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [memLp_two_iff_integrable_sq (aestronglyMeasurable_abkLogKernelProd ..)]
  change Integrable _ ((volume : Measure ℝ).prod (volume : Measure (Vec d)))
  rw [integrable_prod_iff hsq]
  refine ⟨ae_of_all _ (integrable_sq_abkLogKernelProd_section normalization ζ ψ),
    (integrable_abkScaleMajorant (a := (d : ℝ) - 1) (by linarith) C0 Cinf).mono'
      hsq.norm.integral_prod_right' (ae_of_all _ fun r => ?_)⟩
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  by_cases hr : 0 < r
  · by_cases h₁ : r ≤ 1
    · simpa [abkScaleMajorant, Set.mem_Ioc, hr, h₁, not_lt.mpr h₁] using hsmall r hr h₁
    · simpa [abkScaleMajorant, Set.mem_Ioc, h₁, lt_of_not_ge h₁] using hlarge r (le_of_not_ge h₁)
  · have h₁ : ¬1 < r := not_lt.mpr ((le_of_not_gt hr).trans zero_le_one)
    simp [abkScaleMajorant, abkLogKernelProd, Set.mem_Ioc, hr, h₁]

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

/-- Covariance of ABK field evaluations is the deterministic `L²` inner product of their
scale-space kernels. -/
theorem covariance_abkLogCorrelatedFieldL2 {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)
    (hψ :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkLogKernelProd normalization ζ φ) 2
        (volume : Measure (ℝ × Vec d))) :
    cov[abkLogCorrelatedFieldL2 normalization ζ ψ hψ,
        abkLogCorrelatedFieldL2 normalization ζ φ hφ;
        scaleSpaceWhiteNoiseMeasure d] =
      ⟪abkLogKernelLp normalization ζ ψ hψ,
        abkLogKernelLp normalization ζ φ hφ⟫_ℝ := by
  apply covariance_scaleSpaceWhiteNoiseL2 <;> assumption

/-- The deterministic kernel inner product is represented by the integral of the product of
concrete kernels. -/
theorem inner_abkLogKernelLp_eq_integral {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)
    (hψ :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkLogKernelProd normalization ζ φ) 2
        (volume : Measure (ℝ × Vec d))) :
    ⟪abkLogKernelLp normalization ζ ψ hψ,
        abkLogKernelLp normalization ζ φ hφ⟫_ℝ =
      ∫ z : ScaleSpace d,
        abkLogKernel normalization ζ ψ z *
          abkLogKernel normalization ζ φ z := by
  apply inner_toLp_real <;> assumption

/-- Product-coordinate form of the deterministic kernel inner product. -/
theorem inner_abkLogKernelLp_eq_prod_integral {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)
    (hψ :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkLogKernelProd normalization ζ φ) 2
        (volume : Measure (ℝ × Vec d))) :
    ⟪abkLogKernelLp normalization ζ ψ hψ,
        abkLogKernelLp normalization ζ φ hφ⟫_ℝ =
      ∫ p : ℝ × Vec d,
        abkLogKernelProd normalization ζ ψ p *
          abkLogKernelProd normalization ζ φ p := by
  rw [inner_abkLogKernelLp_eq_integral]
  exact (scaleSpaceMeasurePreserving d).integral_comp'
    (f := scaleSpaceMeasurableEquiv d)
    (g := fun p : ℝ × Vec d =>
      abkLogKernelProd normalization ζ ψ p *
        abkLogKernelProd normalization ζ φ p)

/-- Product-coordinate covariance formula for the ABK log-correlated field. -/
theorem covariance_abkLogCorrelatedFieldL2_eq_prod_integral {d : Nat}
    (normalization : ℝ) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)
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
  rw [covariance_abkLogCorrelatedFieldL2,
    inner_abkLogKernelLp_eq_prod_integral]

end GaussianFields

end
