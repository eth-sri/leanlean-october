/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.ScaleLimit.ProductSection

/-!
# GaussianFields ABK power decomposition

Port of the corresponding GaussianFields source module.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

/-- Pair-space form of the ABK power-decomposition integrand. -/
@[expose]
noncomputable def abkPowerDecompositionPairIntegrand {d : Nat}
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) (α : ℝ)
    (r : ℝ) (p : Vec d × Vec d) : ℝ :=
  if 0 < r then
    ψ p.1 * φ p.2 *
      (r ^ (-(1 + (d : ℝ) + α)) *
        abkScaledCutoffSelfConvolution ζ r (p.1 - p.2))
  else
    0

/-- Tail majorant for the pair-space power-decomposition integrand. -/
@[expose]
noncomputable def abkPowerDecompositionPairMajorant {d : Nat}
    (ψ φ : MeanZeroTestFunction d) (α : ℝ)
    (r : ℝ) (p : Vec d × Vec d) : ℝ :=
  |ψ p.1 * φ p.2| *
    (Set.Ici (euclideanNorm (p.1 - p.2) / 2)).indicator
      (fun s : ℝ => (2 : ℝ) ^ d * s ^ (-(1 + α))) r






/-- Abel-regularized scale-product integrals are the power-decomposition/Riesz pairings. -/
theorem integral_abkRegularizedScaleProductSection_eq_mAlphaInv_mul_centeredRiesz
    {d} (hd : 0 < d) (ζ : ABKCutoff d)
    (ψ φ : MeanZeroTestFunction d) {α : ℝ}
    (hα_pos : 0 < α) (hα_le : α ≤ 1 / 2) :
    (∫ r : ℝ, abkRegularizedScaleProductSection ζ ψ φ α r
        ∂(volume : Measure ℝ)) =
      abkMAlphaInv ζ α * abkCenteredRieszDifferencePairing ψ φ α := by
  have integrable_abkPowerDecompositionPairIntegrand_of_pos_le_half {d} (hd : 0 < d) (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (φ : MeanZeroTestFunction d) {α : ℝ} (hα_pos : 0 < α) (hα_le : α ≤ 1 / 2) : Integrable (fun q : (Vec d × Vec d) × ℝ => abkPowerDecompositionPairIntegrand ζ ψ φ α q.2 q.1) (((volume : Measure (Vec d)).prod (volume : Measure (Vec d))).prod (volume : Measure ℝ)) := by
    have aestronglyMeasurable_abkPowerDecompositionPairIntegrand : AEStronglyMeasurable (fun q : (Vec d × Vec d) × ℝ => abkPowerDecompositionPairIntegrand ζ ψ φ α q.2 q.1) (((volume : Measure (Vec d)).prod (volume : Measure (Vec d))).prod (volume : Measure ℝ)) := by
      let μ : Measure ((Vec d × Vec d) × ℝ) :=
        ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))).prod
          (volume : Measure ℝ)
      let S : Set ((Vec d × Vec d) × ℝ) := {q | 0 < q.2}
      refine (AEStronglyMeasurable.piecewise (measurableSet_lt measurable_const continuous_snd.measurable) (((((ψ.continuous.comp (continuous_fst.fst)).mul (φ.continuous.comp (continuous_fst.snd))).aestronglyMeasurable).restrict).mul ((((continuous_snd.measurable.pow_const (-(1 + (d : ℝ) + α))).aestronglyMeasurable : AEStronglyMeasurable (fun q : (Vec d × Vec d) × ℝ => q.2 ^ (-(1 + (d : ℝ) + α))) μ).restrict).mul (show AEStronglyMeasurable (fun q : (Vec d × Vec d) × ℝ => abkScaledCutoffSelfConvolution ζ q.2 (q.1.1 - q.1.2)) μ by simpa [abkScaledCutoffSelfConvolution, μ] using ((show StronglyMeasurable (fun qy : ((Vec d × Vec d) × ℝ) × Vec d => abkScaledCutoff ζ qy.1.2 qy.2 * abkScaledCutoff ζ qy.1.2 (qy.1.1.1 - qy.1.1.2 - qy.2)) by unfold abkScaledCutoff; exact (ζ.continuous.measurable.comp (by fun_prop)).stronglyMeasurable.mul (ζ.continuous.measurable.comp (by fun_prop)).stronglyMeasurable).integral_prod_right' (ν := (volume : Measure (Vec d)))).aestronglyMeasurable).restrict)) (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : (Vec d × Vec d) × ℝ => (0 : ℝ)) (μ.restrict Sᶜ))).congr ?_
      filter_upwards with q
      by_cases hq : q ∈ S
      · have hr : 0 < q.2 := hq
        simp [abkPowerDecompositionPairIntegrand, S, hq, hr, Set.piecewise_eq_of_mem]
      · have hr : ¬ 0 < q.2 := hq
        simp [abkPowerDecompositionPairIntegrand, S, hq, hr, Set.piecewise_eq_of_notMem]
    have integrable_abkPowerDecompositionPairMajorant_of_pos_le_half : Integrable (fun q : (Vec d × Vec d) × ℝ => abkPowerDecompositionPairMajorant ψ φ α q.2 q.1) (((volume : Measure (Vec d)).prod (volume : Measure (Vec d))).prod (volume : Measure ℝ)) := by
      have aestronglyMeasurable_abkPowerDecompositionPairMajorant : AEStronglyMeasurable (fun q : (Vec d × Vec d) × ℝ => abkPowerDecompositionPairMajorant ψ φ α q.2 q.1) (((volume : Measure (Vec d)).prod (volume : Measure (Vec d))).prod (volume : Measure ℝ)) := by
        let S : Set ((Vec d × Vec d) × ℝ) :=
          {q | euclideanNorm (q.1.1 - q.1.2) / 2 ≤ q.2}
        refine ((show AEStronglyMeasurable (fun q : (Vec d × Vec d) × ℝ => |ψ q.1.1 * φ q.1.2| * ((2 : ℝ) ^ d * q.2 ^ (-(1 + α)))) (((volume : Measure (Vec d)).prod (volume : Measure (Vec d))).prod (volume : Measure ℝ)) by exact ((((ψ.continuous.comp (continuous_fst.fst)).mul (φ.continuous.comp (continuous_fst.snd))).abs).aestronglyMeasurable).mul (aestronglyMeasurable_const.mul ((continuous_snd.measurable.pow_const (-(1 + α))).aestronglyMeasurable))).indicator (measurableSet_le (((continuous_euclideanNorm (d := d)).comp ((continuous_fst.fst).sub (continuous_fst.snd))).div_const 2).measurable continuous_snd.measurable)).congr ?_
        filter_upwards with q
        by_cases hq : q ∈ S
        · have htail : q.2 ∈ Set.Ici (euclideanNorm (q.1.1 - q.1.2) / 2) := hq
          simp [abkPowerDecompositionPairMajorant, S, hq, htail, mul_assoc]
        · have htail : q.2 ∉ Set.Ici (euclideanNorm (q.1.1 - q.1.2) / 2) := hq
          simp [abkPowerDecompositionPairMajorant, S, hq, htail]
      let μ : Measure (Vec d × Vec d) :=
        (volume : Measure (Vec d)).prod (volume : Measure (Vec d))
      let F : (Vec d × Vec d) × ℝ → ℝ := fun q =>
        abkPowerDecompositionPairMajorant ψ φ α q.2 q.1
      have hF_meas : AEStronglyMeasurable F (μ.prod (volume : Measure ℝ)) := by
        simpa [F, μ] using aestronglyMeasurable_abkPowerDecompositionPairMajorant
      refine (integrable_prod_iff hF_meas).2 ?_
      constructor
      · filter_upwards [ae_fst_ne_snd_volume_prod hd] with p hp_ne
        have : 0 < euclideanNorm (p.1 - p.2) :=
          abkEuclideanNorm_pos_of_ne_zero (by intro hzero; exact hp_ne (sub_eq_zero.mp hzero))
        have hconst :
            Integrable
              ((Set.Ici (euclideanNorm (p.1 - p.2) / 2)).indicator
                (fun r => (2 : ℝ) ^ d * r ^ (-(1 + α))))
              (volume : Measure ℝ) := by
          convert (integrable_indicator_Ici_rpow_neg_one_sub hα_pos (show 0 < euclideanNorm (p.1 - p.2) / 2 by positivity)).const_mul ((2 : ℝ) ^ d) using 1
          funext r
          by_cases hr : r ∈ Set.Ici (euclideanNorm (p.1 - p.2) / 2)
          · simp [hr]
          · simp [hr]
        simpa [F, abkPowerDecompositionPairMajorant, mul_assoc] using
          hconst.const_mul |ψ p.1 * φ p.2|
      · have hmeas_int :
            AEStronglyMeasurable
              (fun p => ∫ r : ℝ, ‖F (p, r)‖ ∂(volume : Measure ℝ))
              μ :=
          hF_meas.norm.integral_prod_right'
        let C := (2 : ℝ) ^ d * (2 / α)
        refine ((integrable_abkRieszKernel_integrand_of_pos_le_half hd ψ φ hα_pos hα_le).norm.const_mul C).mono' hmeas_int ?_
        filter_upwards [ae_fst_ne_snd_volume_prod hd] with p hp_ne
        have hρ_pos := abkEuclideanNorm_pos_of_ne_zero (by intro hzero; exact hp_ne (sub_eq_zero.mp hzero))
        have hnonneg : ∀ r : ℝ, 0 ≤ F (p, r) := by
          intro r
          unfold F abkPowerDecompositionPairMajorant
          refine mul_nonneg (abs_nonneg _) ?_
          by_cases hr : r ∈ Set.Ici (euclideanNorm (p.1 - p.2) / 2)
          · rw [Set.indicator_of_mem hr]
            exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d)
              (Real.rpow_nonneg (by exact (show 0 ≤ euclideanNorm (p.1 - p.2) / 2 by positivity).trans hr) _)
          · rw [Set.indicator_of_notMem hr]
        have hnorm_eq :
            (∫ r : ℝ, ‖F (p, r)‖ ∂(volume : Measure ℝ)) =
              ∫ r : ℝ, F (p, r) ∂(volume : Measure ℝ) := by
          refine integral_congr_ae ?_
          filter_upwards with r
          rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg r)]
        have hmain_eq :
            (∫ r : ℝ, F (p, r) ∂(volume : Measure ℝ)) =
              |ψ p.1 * φ p.2| *
                ((2 : ℝ) ^ d *
                  ((euclideanNorm (p.1 - p.2) / 2) ^ (-α) / α)) := by
          have hconst_integral :
              (∫ r : ℝ,
                  (Set.Ici (euclideanNorm (p.1 - p.2) / 2)).indicator
                    (fun s => (2 : ℝ) ^ d * s ^ (-(1 + α))) r
                  ∂(volume : Measure ℝ)) =
                (2 : ℝ) ^ d *
                  ∫ r : ℝ,
                    (Set.Ici (euclideanNorm (p.1 - p.2) / 2)).indicator
                      (fun s => s ^ (-(1 + α))) r
                    ∂(volume : Measure ℝ) := by
            rw [← integral_const_mul]
            refine integral_congr_ae ?_
            filter_upwards with r
            by_cases hr : r ∈ Set.Ici (euclideanNorm (p.1 - p.2) / 2)
            · simp [hr]
            · simp [hr]
          change
            (∫ r : ℝ,
              |ψ p.1 * φ p.2| *
                (Set.Ici (euclideanNorm (p.1 - p.2) / 2)).indicator
                  (fun s => (2 : ℝ) ^ d * s ^ (-(1 + α))) r
              ∂(volume : Measure ℝ)) =
            |ψ p.1 * φ p.2| *
              ((2 : ℝ) ^ d *
                ((euclideanNorm (p.1 - p.2) / 2) ^ (-α) / α))
          rw [integral_const_mul, hconst_integral, (integral_indicator_Ici_rpow_neg_one_sub hα_pos (show 0 < euclideanNorm (p.1 - p.2) / 2 by positivity))]
        have hdiv_bound :
            (euclideanNorm (p.1 - p.2) / 2) ^ (-α) ≤
              2 * (euclideanNorm (p.1 - p.2)) ^ (-α) := by
          calc
            (euclideanNorm (p.1 - p.2) / 2) ^ (-α)
                = (euclideanNorm (p.1 - p.2)) ^ (-α) * (1 / 2 : ℝ) ^ (-α) := (by rw [div_eq_mul_inv, Real.mul_rpow hρ_pos.le (by norm_num : 0 ≤ (2 : ℝ)⁻¹)]; ring_nf)
            _ = (euclideanNorm (p.1 - p.2)) ^ (-α) * (2 : ℝ) ^ α := by rw [(show (1 / 2 : ℝ) ^ (-α) = (2 : ℝ) ^ α by rw [Real.rpow_neg (show 0 < (1 / 2 : ℝ) by norm_num).le, Real.div_rpow (by norm_num : 0 ≤ (1 : ℝ)) (by norm_num : 0 ≤ (2 : ℝ))]; simp [Real.one_rpow])]
            _ ≤ (euclideanNorm (p.1 - p.2)) ^ (-α) * 2 := by
              exact mul_le_mul_of_nonneg_left (by simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (show α ≤ (1 : ℝ) by linarith))
                (Real.rpow_nonneg hρ_pos.le _)
            _ = 2 * (euclideanNorm (p.1 - p.2)) ^ (-α) := by ring_nf
        calc
          ‖∫ r : ℝ, ‖F (p, r)‖ ∂(volume : Measure ℝ)‖
              = ∫ r : ℝ, ‖F (p, r)‖ ∂(volume : Measure ℝ) := by
                rw [Real.norm_eq_abs, abs_of_nonneg]
                exact integral_nonneg fun r => norm_nonneg _
          _ = |ψ p.1 * φ p.2| *
                ((2 : ℝ) ^ d *
                  ((euclideanNorm (p.1 - p.2) / 2) ^ (-α) / α)) := by
                rw [hnorm_eq, hmain_eq]
          _ ≤ C * ‖ψ p.1 * φ p.2 * abkRieszKernel α p.1 p.2‖ := by
            rw [(show ‖ψ p.1 * φ p.2 * abkRieszKernel α p.1 p.2‖ = |ψ p.1 * φ p.2| * (euclideanNorm (p.1 - p.2)) ^ (-α) by rw [Real.norm_eq_abs, abs_mul, abkRieszKernel, abs_of_nonneg (Real.rpow_nonneg (euclideanNorm_nonneg _) _)])]
            dsimp [C]
            calc
              |ψ p.1 * φ p.2| *
                  ((2 : ℝ) ^ d *
                    ((euclideanNorm (p.1 - p.2) / 2) ^ (-α) / α))
                  ≤ |ψ p.1 * φ p.2| *
                      ((2 : ℝ) ^ d *
                        ((2 * (euclideanNorm (p.1 - p.2)) ^ (-α)) / α)) := by
                    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
                    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                    exact div_le_div_of_nonneg_right hdiv_bound hα_pos.le
              _ = ((2 : ℝ) ^ d * (2 / α)) *
                    (|ψ p.1 * φ p.2| *
                      (euclideanNorm (p.1 - p.2)) ^ (-α)) := by ring_nf
    have norm_abkPowerDecompositionPairIntegrand_le_majorant {α : ℝ} {r : ℝ} p : ‖abkPowerDecompositionPairIntegrand ζ ψ φ α r p‖ ≤ abkPowerDecompositionPairMajorant ψ φ α r p := by
      let ρ : ℝ := euclideanNorm (p.1 - p.2)
      have : 0 ≤ ρ := euclideanNorm_nonneg _
      by_cases hr : 0 < r
      · by_cases htail : r ∈ Set.Ici (ρ / 2)
        · have hself_nonneg :
              0 ≤ abkScaledCutoffSelfConvolution ζ r (p.1 - p.2) :=
            abkScaledCutoffSelfConvolution_nonneg ζ r (p.1 - p.2)
          have hpow_nonneg :
              0 ≤ r ^ (-(1 + (d : ℝ) + α)) := Real.rpow_nonneg hr.le _
          have hkernel_bound :
              r ^ (-(1 + (d : ℝ) + α)) *
                  abkScaledCutoffSelfConvolution ζ r (p.1 - p.2) ≤
                (2 : ℝ) ^ d * r ^ (-(1 + α)) := by
            calc
              r ^ (-(1 + (d : ℝ) + α)) *
                  abkScaledCutoffSelfConvolution ζ r (p.1 - p.2)
                  ≤ r ^ (-(1 + (d : ℝ) + α)) * (2 * r) ^ d :=
                    mul_le_mul_of_nonneg_left (abkScaledCutoffSelfConvolution_le_pow ζ hr (p.1 - p.2)) hpow_nonneg
              _ = (2 : ℝ) ^ d * r ^ (-(1 + α)) := by
                rw [mul_pow]
                rw [(show r ^ d = r ^ (d : ℝ) by rw [Real.rpow_natCast])]
                calc
                  r ^ (-(1 + (d : ℝ) + α)) * ((2 : ℝ) ^ d * r ^ (d : ℝ))
                      = (2 : ℝ) ^ d *
                          (r ^ (-(1 + (d : ℝ) + α)) * r ^ (d : ℝ)) := by ring_nf
                  _ = (2 : ℝ) ^ d *
                        r ^ (-(1 + (d : ℝ) + α) + (d : ℝ)) := by
                      rw [Real.rpow_add hr]
                  _ = (2 : ℝ) ^ d * r ^ (-(1 + α)) := by
                      congr 1
                      ring_nf
          calc
            ‖abkPowerDecompositionPairIntegrand ζ ψ φ α r p‖
                = |ψ p.1 * φ p.2| *
                    (r ^ (-(1 + (d : ℝ) + α)) *
                      abkScaledCutoffSelfConvolution ζ r (p.1 - p.2)) := by
                  rw [abkPowerDecompositionPairIntegrand, ite_eq_left hr, Real.norm_eq_abs,
                    abs_mul]
                  rw [abs_of_nonneg (mul_nonneg hpow_nonneg hself_nonneg)]
            _ ≤ |ψ p.1 * φ p.2| *
                  ((2 : ℝ) ^ d * r ^ (-(1 + α))) :=
                  mul_le_mul_of_nonneg_left hkernel_bound (abs_nonneg _)
            _ = abkPowerDecompositionPairMajorant ψ φ α r p := by
                  simp [abkPowerDecompositionPairMajorant, ρ, htail]
        · have hr_lt : r < ρ / 2 := lt_of_not_ge htail
          simp [abkPowerDecompositionPairIntegrand, abkPowerDecompositionPairMajorant,
            hr, (by simpa [ρ] using htail), (by apply abkScaledCutoffSelfConvolution_eq_zero_of_two_mul_lt_norm ζ hr; dsimp [ρ] at hr_lt ⊢; linarith)]
      · have hnonneg_majorant :
            0 ≤ abkPowerDecompositionPairMajorant ψ φ α r p := by
          unfold abkPowerDecompositionPairMajorant
          refine mul_nonneg (abs_nonneg _) ?_
          by_cases htail : r ∈ Set.Ici (ρ / 2)
          · rw [Set.indicator_of_mem htail]
            exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d)
              (Real.rpow_nonneg (by exact (show 0 ≤ ρ / 2 by positivity).trans htail) _)
          · rw [Set.indicator_of_notMem htail]
        simpa [abkPowerDecompositionPairIntegrand, hr] using hnonneg_majorant
    let μ : Measure ((Vec d × Vec d) × ℝ) :=
      ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))).prod
        (volume : Measure ℝ)
    let F : (Vec d × Vec d) × ℝ → ℝ := fun q =>
      abkPowerDecompositionPairIntegrand ζ ψ φ α q.2 q.1
    let G : (Vec d × Vec d) × ℝ → ℝ := fun q =>
      abkPowerDecompositionPairMajorant ψ φ α q.2 q.1
    refine (show Integrable G μ by simpa [G, μ] using integrable_abkPowerDecompositionPairMajorant_of_pos_le_half).mono' (by simpa [F, μ] using aestronglyMeasurable_abkPowerDecompositionPairIntegrand) ?_
    filter_upwards with q
    simpa [F, G] using
      norm_abkPowerDecompositionPairIntegrand_le_majorant (α := α) (r := q.2) q.1
  let μ : Measure (Vec d × Vec d) :=
    (volume : Measure (Vec d)).prod (volume : Measure (Vec d))
  let F : (Vec d × Vec d) × ℝ → ℝ := fun q =>
    abkPowerDecompositionPairIntegrand ζ ψ φ α q.2 q.1
  have hF_int : Integrable F (μ.prod (volume : Measure ℝ)) := by
    simpa [F, μ] using
      integrable_abkPowerDecompositionPairIntegrand_of_pos_le_half
        hd ζ ψ φ hα_pos hα_le
  have hR := integrable_abkRieszKernel_integrand_of_pos_le_half hd ψ φ hα_pos hα_le
  have hscale :
      (∫ r : ℝ, abkRegularizedScaleProductSection ζ ψ φ α r
          ∂(volume : Measure ℝ)) =
        ∫ r : ℝ, ∫ p : Vec d × Vec d, F (p, r) ∂μ
          ∂(volume : Measure ℝ) := by
    refine integral_congr_ae ?_
    filter_upwards [hF_int.prod_left_ae] with r hp_int
    by_cases hr : 0 < r
    · have hprod :
          (∫ p : Vec d × Vec d, F (p, r) ∂μ) =
            r ^ (-(1 + (d : ℝ) + α)) *
              (∫ x : Vec d,
                ψ x *
                  (∫ z : Vec d,
                    φ z * abkScaledCutoffSelfConvolution ζ r (x - z)
                    ∂(volume : Measure (Vec d)))
                ∂(volume : Measure (Vec d))) := by
        rw [integral_prod _ hp_int]
        calc
          (∫ x : Vec d,
              ∫ z : Vec d, F ((x, z), r) ∂(volume : Measure (Vec d))
              ∂(volume : Measure (Vec d)))
              = ∫ x : Vec d,
                  ∫ z : Vec d,
                    ψ x * φ z *
                      (r ^ (-(1 + (d : ℝ) + α)) *
                        abkScaledCutoffSelfConvolution ζ r (x - z))
                    ∂(volume : Measure (Vec d))
                  ∂(volume : Measure (Vec d)) := by
                refine integral_congr_ae ?_
                filter_upwards with x
                refine integral_congr_ae ?_
                filter_upwards with z
                simp [F, abkPowerDecompositionPairIntegrand, hr]
          _ = ∫ x : Vec d,
                ψ x *
                  (∫ z : Vec d,
                    φ z *
                      (r ^ (-(1 + (d : ℝ) + α)) *
                        abkScaledCutoffSelfConvolution ζ r (x - z))
                    ∂(volume : Measure (Vec d)))
                ∂(volume : Measure (Vec d)) := by
                refine integral_congr_ae ?_
                filter_upwards with x
                rw [← integral_const_mul]
                refine integral_congr_ae ?_
                filter_upwards with z
                ring_nf
          _ = ∫ x : Vec d,
                ψ x *
                  (r ^ (-(1 + (d : ℝ) + α)) *
                    (∫ z : Vec d,
                      φ z * abkScaledCutoffSelfConvolution ζ r (x - z)
                      ∂(volume : Measure (Vec d))))
                ∂(volume : Measure (Vec d)) := by
                refine integral_congr_ae ?_
                filter_upwards with x
                congr 1
                calc
                  (∫ z : Vec d,
                    φ z *
                      (r ^ (-(1 + (d : ℝ) + α)) *
                        abkScaledCutoffSelfConvolution ζ r (x - z))
                    ∂(volume : Measure (Vec d)))
                      = ∫ z : Vec d,
                          r ^ (-(1 + (d : ℝ) + α)) *
                            (φ z * abkScaledCutoffSelfConvolution ζ r (x - z))
                          ∂(volume : Measure (Vec d)) := by
                            refine integral_congr_ae ?_
                            filter_upwards with z
                            ring_nf
                  _ = r ^ (-(1 + (d : ℝ) + α)) *
                        (∫ z : Vec d,
                          φ z * abkScaledCutoffSelfConvolution ζ r (x - z)
                          ∂(volume : Measure (Vec d))) := by
                            rw [integral_const_mul]
          _ = r ^ (-(1 + (d : ℝ) + α)) *
                (∫ x : Vec d,
                  ψ x *
                    (∫ z : Vec d,
                      φ z * abkScaledCutoffSelfConvolution ζ r (x - z)
                      ∂(volume : Measure (Vec d)))
                  ∂(volume : Measure (Vec d))) := by
                rw [← integral_const_mul]
                refine integral_congr_ae ?_
                filter_upwards with x
                ring_nf
      rw [hprod]
      let A := ∫ x : Vec d,
          ψ x *
            (∫ z : Vec d,
              φ z * abkScaledCutoffSelfConvolution ζ r (x - z)
              ∂(volume : Measure (Vec d)))
          ∂(volume : Measure (Vec d))
      calc
        abkRegularizedScaleProductSection ζ ψ φ α r
            = r ^ (-α) * abkScaleProductSection ζ ψ φ r := by
              simp [abkRegularizedScaleProductSection, hr]
        _ = r ^ (-α) * (r ^ (-((d : ℝ) + 1)) * A) := by
              rw [abkScaleProductSection_eq_selfConvolution_integral_of_pos ζ ψ φ hr]
        _ = r ^ (-(1 + (d : ℝ) + α)) * A := by
              calc
                r ^ (-α) * (r ^ (-((d : ℝ) + 1)) * A)
                    = (r ^ (-α) * r ^ (-((d : ℝ) + 1))) * A := by ring_nf
                _ = r ^ (-α + -((d : ℝ) + 1)) * A := by
                    rw [Real.rpow_add hr]
                _ = r ^ (-(1 + (d : ℝ) + α)) * A := by
                    congr 1
                    ring_nf
    · have hprod_zero :
          (∫ p : Vec d × Vec d, F (p, r) ∂μ) = 0 := by
        refine integral_eq_zero_of_ae ?_
        filter_upwards with p
        simp [F, abkPowerDecompositionPairIntegrand, hr]
      rw [hprod_zero]
      simp [abkRegularizedScaleProductSection, hr]
  have hpair :
      (∫ p : Vec d × Vec d, ∫ r : ℝ, F (p, r) ∂(volume : Measure ℝ) ∂μ) =
        abkMAlphaInv ζ α * abkRieszPairing ψ φ α := by
    have hinner :
        (fun p : Vec d × Vec d => ∫ r : ℝ, F (p, r) ∂(volume : Measure ℝ)) =
          fun p : Vec d × Vec d =>
            ψ p.1 * φ p.2 *
              (∫ r in Set.Ioi (0 : ℝ),
                r ^ (-(1 + (d : ℝ) + α)) *
                  abkScaledCutoffSelfConvolution ζ r (p.1 - p.2)
                ∂(volume : Measure ℝ)) := by
      funext p
      unfold F abkPowerDecompositionPairIntegrand
      change
        (∫ r : ℝ,
          (Set.Ioi (0 : ℝ)).indicator
            (fun r : ℝ =>
            ψ p.1 * φ p.2 *
              (r ^ (-(1 + (d : ℝ) + α)) *
                abkScaledCutoffSelfConvolution ζ r (p.1 - p.2))) r) =
        ψ p.1 * φ p.2 *
          (∫ r in Set.Ioi (0 : ℝ),
            r ^ (-(1 + (d : ℝ) + α)) *
              abkScaledCutoffSelfConvolution ζ r (p.1 - p.2)
            ∂(volume : Measure ℝ))
      rw [integral_indicator measurableSet_Ioi, integral_const_mul]
    rw [hinner]
    have hleft_prod :
        (∫ p : Vec d × Vec d,
            ψ p.1 * φ p.2 *
              (∫ r in Set.Ioi (0 : ℝ),
                r ^ (-(1 + (d : ℝ) + α)) *
                  abkScaledCutoffSelfConvolution ζ r (p.1 - p.2)
                ∂(volume : Measure ℝ)) ∂μ) =
          ∫ x : Vec d,
            ψ x *
              (∫ z : Vec d,
                φ z *
                  (∫ r in Set.Ioi (0 : ℝ),
                    r ^ (-(1 + (d : ℝ) + α)) *
                      abkScaledCutoffSelfConvolution ζ r (x - z)
                    ∂(volume : Measure ℝ))
                ∂(volume : Measure (Vec d)))
            ∂(volume : Measure (Vec d)) := by
      rw [integral_prod _ (show Integrable (fun p : Vec d × Vec d => ψ p.1 * φ p.2 * (∫ r in Set.Ioi (0 : ℝ), r ^ (-(1 + (d : ℝ) + α)) * abkScaledCutoffSelfConvolution ζ r (p.1 - p.2) ∂(volume : Measure ℝ))) μ by simpa [hinner] using hF_int.integral_prod_left)]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards with z
      ring_nf
    have hR_iter :
        abkRieszPairing ψ φ α =
          ∫ x : Vec d,
            ψ x *
              (∫ z : Vec d,
                φ z * (euclideanNorm (x - z)) ^ (-α)
                ∂(volume : Measure (Vec d)))
          ∂(volume : Measure (Vec d)) := by
      unfold abkRieszPairing
      rw [abkKernelPairing_eq_integral_integral ψ φ (abkRieszKernel α) hR]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards with z
      simp [abkRieszKernel]
      ring_nf
    calc
      (∫ p : Vec d × Vec d,
          ψ p.1 * φ p.2 *
            (∫ r in Set.Ioi (0 : ℝ),
              r ^ (-(1 + (d : ℝ) + α)) *
                abkScaledCutoffSelfConvolution ζ r (p.1 - p.2)
              ∂(volume : Measure ℝ)) ∂μ)
          = ∫ x : Vec d,
            ψ x *
              (∫ z : Vec d,
                φ z *
                  (∫ r in Set.Ioi (0 : ℝ),
                    r ^ (-(1 + (d : ℝ) + α)) *
                      abkScaledCutoffSelfConvolution ζ r (x - z)
                    ∂(volume : Measure ℝ))
                ∂(volume : Measure (Vec d)))
            ∂(volume : Measure (Vec d)) := hleft_prod
      _ = abkMAlphaInv ζ α *
            (∫ x : Vec d,
              ψ x *
                (∫ z : Vec d,
                  φ z * (euclideanNorm (x - z)) ^ (-α)
                  ∂(volume : Measure (Vec d)))
              ∂(volume : Measure (Vec d))) := (integral_integral_abkPowerDecomposition_kernel_eq_riesz_pairing hd ζ ψ φ α)
      _ = abkMAlphaInv ζ α * abkRieszPairing ψ φ α := by rw [hR_iter]
  calc
    (∫ r : ℝ, abkRegularizedScaleProductSection ζ ψ φ α r
        ∂(volume : Measure ℝ))
        = ∫ r : ℝ, ∫ p : Vec d × Vec d, F (p, r) ∂μ
            ∂(volume : Measure ℝ) := hscale
    _ = ∫ p : Vec d × Vec d, ∫ r : ℝ, F (p, r) ∂(volume : Measure ℝ) ∂μ := (by exact (integral_integral_swap (μ := μ) (ν := (volume : Measure ℝ)) (f := fun p => fun r => F (p, r)) hF_int).symm)
    _ = abkMAlphaInv ζ α * abkRieszPairing ψ φ α := hpair
    _ = abkMAlphaInv ζ α * abkCenteredRieszDifferencePairing ψ φ α := by
      rw [abkCenteredRieszDifferencePairing_eq_rieszPairing ψ φ α hR]

end GaussianFields

end
