/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.Volume
public import GaussianFields.LogCorrelated.ABK.SpatialFubini

/-!
# GaussianFields.LogCorrelated/ABK/Covariance

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

/-- The canonically normalized ABK product kernel is in `L²`. -/
theorem memLp_abkLogKernelProd_canonical {d : Nat} (hd : 0 < d)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) :
    MemLp (abkLogKernelProd (abkNormalization ζ) ζ ψ) 2
      (volume : Measure (ℝ × Vec d)) :=
  memLp_abkLogKernelProd_of_abk_estimates hd

/-- The canonically normalized ABK log-correlated field evaluation. -/
@[expose]
noncomputable def abkLogCorrelatedFieldL2Canonical {d : Nat} (hd : 0 < d)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) :
    Lp ℝ 2 (scaleSpaceWhiteNoiseMeasure d) :=
  abkLogCorrelatedFieldL2 (abkNormalization ζ) ζ ψ
    (memLp_abkLogKernelProd_canonical hd ζ ψ)

/-- Canonical covariance after the fixed-scale spatial Fubini rearrangement.  The spatial section
is the double integral against the scaled cutoff self-convolution. -/
theorem covariance_abkLogCorrelatedFieldL2Canonical_eq_scale_selfConvolution_integral
    {d : Nat} (hd : 0 < d) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) :
    cov[abkLogCorrelatedFieldL2Canonical hd ζ ψ,
        abkLogCorrelatedFieldL2Canonical hd ζ φ;
        scaleSpaceWhiteNoiseMeasure d] =
      ∫ r : ℝ,
        if 0 < r then
          abkNormalizationRadicand ζ * r ^ (-((d : ℝ) + 1)) *
            (∫ x : Vec d,
              ψ x *
                (∫ z : Vec d,
                  φ z * abkScaledCutoffSelfConvolution ζ r (x - z)
                  ∂(volume : Measure (Vec d)))
              ∂(volume : Measure (Vec d)))
        else
          0 := by
  let hψ := memLp_abkLogKernelProd_canonical hd ζ ψ
  let hφ := memLp_abkLogKernelProd_canonical hd ζ φ
  unfold abkLogCorrelatedFieldL2Canonical
  rw [covariance_abkLogCorrelatedFieldL2_eq_prod_integral]
  have hprod_int :
      Integrable
        (fun p : ℝ × Vec d =>
          abkLogKernelProd (abkNormalization ζ) ζ ψ p *
            abkLogKernelProd (abkNormalization ζ) ζ φ p)
        (volume : Measure _) := by
    change Integrable
      (abkLogKernelProd (abkNormalization ζ) ζ ψ *
        abkLogKernelProd (abkNormalization ζ) ζ φ)
      (volume : Measure _)
    exact hψ.integrable_mul hφ
  rw [Measure.volume_eq_prod] at hprod_int ⊢
  rw [integral_prod _ hprod_int]
  refine integral_congr_ae ?_
  filter_upwards with r
  by_cases hr : 0 < r
  · have hinner :
        (∫ y : Vec d,
            abkLogKernelProd (abkNormalization ζ) ζ ψ (r, y) *
              abkLogKernelProd (abkNormalization ζ) ζ φ (r, y)
            ∂(volume : Measure (Vec d))) =
          (abkNormalization ζ) ^ (2 : Nat) * r ^ (-((d : ℝ) + 1)) *
            (∫ y : Vec d,
              abkSpatialConvolution ζ ψ r y *
                abkSpatialConvolution ζ φ r y
              ∂(volume : Measure (Vec d))) := by
      let c := (abkNormalization ζ) ^ (2 : Nat) * r ^ (-((d : ℝ) + 1))
      calc
        (∫ y : Vec d,
            abkLogKernelProd (abkNormalization ζ) ζ ψ _ *
              abkLogKernelProd (abkNormalization ζ) ζ φ _
            ∂(volume : Measure (Vec d)))
            = ∫ y : Vec d,
                c *
                  (abkSpatialConvolution ζ ψ r y *
                    abkSpatialConvolution ζ φ r y)
                ∂(volume : Measure (Vec d)) := by
              refine integral_congr_ae ?_
              filter_upwards with y
              rw [abkLogKernelProd_mul, ite_eq_left hr]
        _ = c *
              (∫ y : Vec d,
                abkSpatialConvolution ζ ψ r y *
                  abkSpatialConvolution ζ φ r y
                ∂volume) := by
              rw [integral_const_mul]
    rw [hinner]
    rw [integral_abkSpatialConvolution_mul_abkSpatialConvolution_eq_selfConvolution_integral
      ζ ψ φ hr]
    rw [abkNormalization_sq ζ (abkNormalizationRadicand_nonneg ζ), ite_eq_left hr]
  · have hinner_zero :
        (∫ y : Vec d,
            abkLogKernelProd (abkNormalization ζ) ζ ψ (r, y) *
              abkLogKernelProd (abkNormalization ζ) ζ φ (r, y)
            ∂volume) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards with y
      rw [abkLogKernelProd_mul, ite_eq_right hr]
      simp
    simp_all

end GaussianFields

end
