/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.ScaleLimit.ProductSection

/-!
# GaussianFields ABK power decomposition
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

variable {d : Nat}

private noncomputable def pairInt
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) (α r : ℝ) (p : Vec d × Vec d) : ℝ :=
  if 0 < r then
    ψ p.1 * φ p.2 * (r ^ (-(1 + (d : ℝ) + α)) * abkScaledCutoffSelfConvolution ζ r (p.1 - p.2))
  else 0

private noncomputable def pairMaj
    (ψ φ : MeanZeroTestFunction d) (α r : ℝ) (p : Vec d × Vec d) : ℝ :=
  |ψ p.1 * φ p.2| *
    (Set.Ici (euclideanNorm (p.1 - p.2) / 2)).indicator (fun s : ℝ => (2 : ℝ) ^ d * s ^ (-(1 + α))) r


/-- Abel-regularized scale-product integrals are the power-decomposition/Riesz pairings. -/
theorem integral_abkRegularizedScaleProductSection_eq_mAlphaInv_mul_centeredRiesz
    (hd : 0 < d) (ζ : ABKCutoff d)
    (ψ φ : MeanZeroTestFunction d) {α : ℝ}
    (hα_pos : 0 < α) (hα_le : α ≤ 1 / 2) :
    (∫ r : ℝ, abkRegularizedScaleProductSection ζ ψ φ α r ∂(volume : Measure ℝ)) =
      abkMAlphaInv ζ α * abkCenteredRieszDifferencePairing ψ φ α := by
  have norm_pairInt_le_pairMaj {α r : ℝ} (p : Vec d × Vec d) : ‖pairInt ζ ψ φ α r p‖ ≤ pairMaj ψ φ α r p := by
    let ρ := euclideanNorm (p.1 - p.2)
    by_cases hr : 0 < r
    · by_cases htail : r ∈ Set.Ici (ρ / 2)
      · have hself := abkScaledCutoffSelfConvolution_nonneg ζ r (p.1 - p.2)
        have hpow : 0 ≤ r ^ (-(1 + (d : ℝ) + α)) := Real.rpow_nonneg hr.le _
        have hkb : r ^ (-(1 + (d : ℝ) + α)) * abkScaledCutoffSelfConvolution ζ r (p.1 - p.2) ≤
            (2 : ℝ) ^ d * r ^ (-(1 + α)) := by
          refine (mul_le_mul_of_nonneg_left (abkScaledCutoffSelfConvolution_le_pow ζ hr (p.1 - p.2)) hpow).trans_eq ?_
          rw [mul_pow, ← Real.rpow_natCast r d]
          calc r ^ (-(1 + (d : ℝ) + α)) * ((2 : ℝ) ^ d * r ^ (d : ℝ))
            _ = (2 : ℝ) ^ d * (r ^ (-(1 + (d : ℝ) + α)) * r ^ (d : ℝ)) := by ring
            _ = (2 : ℝ) ^ d * r ^ (-(1 + α)) := by rw [← Real.rpow_add hr]; congr 1; ring
        simp only [pairInt, hr, ↓reduceIte, Real.norm_eq_abs]
        rw [abs_mul, abs_of_nonneg (mul_nonneg hpow hself), pairMaj, Set.indicator_of_mem htail]
        exact mul_le_mul_of_nonneg_left hkb (abs_nonneg _)
      · have hzero := abkScaledCutoffSelfConvolution_eq_zero_of_two_mul_lt_norm ζ hr
          (by linarith [lt_of_not_ge htail] : 2 * r < ρ)
        simp [pairInt, pairMaj, hr, show r ∉ Set.Ici (euclideanNorm (p.1 - p.2) / 2) from htail, hzero]
    · simp only [pairInt, hr, ↓reduceIte, norm_zero, pairMaj]
      refine mul_nonneg (abs_nonneg _) ?_
      by_cases htail : r ∈ Set.Ici (euclideanNorm (p.1 - p.2) / 2)
      · rw [Set.indicator_of_mem htail]
        have hr0 : 0 ≤ r := (div_nonneg (euclideanNorm_nonneg _) zero_le_two).trans htail
        positivity
      · simp [htail]
  let μ := (volume : Measure (Vec d)).prod (volume : Measure (Vec d))
  let ν := μ.prod (volume : Measure ℝ)
  let F (q : (Vec d × Vec d) × ℝ) : ℝ := pairInt ζ ψ φ α q.2 q.1
  let G (q : (Vec d × Vec d) × ℝ) : ℝ := pairMaj ψ φ α q.2 q.1
  have hR := integrable_abkRieszKernel_integrand_of_pos_le_half hd ψ φ hα_pos hα_le
  have hG_meas : AEStronglyMeasurable G ν := by
    let S : Set ((Vec d × Vec d) × ℝ) := {q | euclideanNorm (q.1.1 - q.1.2) / 2 ≤ q.2}
    have hS : MeasurableSet S := measurableSet_le
      (((continuous_euclideanNorm (d := d)).comp (continuous_fst.fst.sub continuous_fst.snd)).div_const 2).measurable
      continuous_snd.measurable
    have hbase : AEStronglyMeasurable
        (fun q : (Vec d × Vec d) × ℝ => |ψ q.1.1 * φ q.1.2| * ((2 : ℝ) ^ d * q.2 ^ (-(1 + α)))) ν :=
      (((ψ.continuous.comp continuous_fst.fst).mul (φ.continuous.comp continuous_fst.snd)).abs.aestronglyMeasurable).mul
        (aestronglyMeasurable_const.mul (continuous_snd.measurable.pow_const _).aestronglyMeasurable)
    refine (hbase.indicator hS).congr (ae_of_all _ fun q => ?_)
    by_cases hq : q ∈ S <;> simp [G, pairMaj, S, hq, show q.2 ∈ Set.Ici _ ↔ q ∈ S from Iff.rfl]
  have hG_int : Integrable G ν := by
    refine (integrable_prod_iff hG_meas).2 ⟨?_, ?_⟩
    · filter_upwards [ae_fst_ne_snd_volume_prod hd] with p hp
      have hc : 0 < euclideanNorm (p.1 - p.2) / 2 :=
        half_pos (abkEuclideanNorm_pos_of_ne_zero (sub_ne_zero.2 hp))
      have hi : Integrable ((Set.Ici (euclideanNorm (p.1 - p.2) / 2)).indicator
          (fun r : ℝ => (2 : ℝ) ^ d * r ^ (-(1 + α)))) volume := by
        convert (integrable_indicator_Ici_rpow_neg_one_sub hα_pos hc).const_mul ((2 : ℝ) ^ d) using 1
        ext r; by_cases hr : r ∈ Set.Ici (euclideanNorm (p.1 - p.2) / 2) <;> simp [hr]
      simpa [G, pairMaj] using hi.const_mul |ψ p.1 * φ p.2|
    · let C := (2 : ℝ) ^ d * (2 / α)
      refine (hR.norm.const_mul C).mono' hG_meas.norm.integral_prod_right' ?_
      filter_upwards [ae_fst_ne_snd_volume_prod hd] with p hp
      have hρ := abkEuclideanNorm_pos_of_ne_zero (sub_ne_zero.2 hp)
      have hc : 0 < euclideanNorm (p.1 - p.2) / 2 := half_pos hρ
      have hnn (r : ℝ) : 0 ≤ G (p, r) :=
        (norm_nonneg (pairInt ζ ψ φ α r p)).trans (norm_pairInt_le_pairMaj p)
      have hint_eq : (∫ r : ℝ, ‖G (p, r)‖) =
          |ψ p.1 * φ p.2| * ((2 : ℝ) ^ d * ((euclideanNorm (p.1 - p.2) / 2) ^ (-α) / α)) := by
        have h1 : (∫ r : ℝ, ‖G (p, r)‖) = ∫ r : ℝ, G (p, r) :=
          integral_congr_ae (ae_of_all _ fun r => Real.norm_of_nonneg (hnn r))
        have h2 : (∫ r : ℝ, (Set.Ici (euclideanNorm (p.1 - p.2) / 2)).indicator
            (fun s : ℝ => (2 : ℝ) ^ d * s ^ (-(1 + α))) r) =
            (2 : ℝ) ^ d * ((euclideanNorm (p.1 - p.2) / 2) ^ (-α) / α) := by
          rw [← integral_indicator_Ici_rpow_neg_one_sub hα_pos hc, ← integral_const_mul]
          exact integral_congr_ae (ae_of_all _ fun r => by
            dsimp only; by_cases hr : r ∈ Set.Ici (euclideanNorm (p.1 - p.2) / 2) <;> simp [hr])
        rw [h1]; dsimp [G, pairMaj]; rw [integral_const_mul, h2]
      have hdiv : (euclideanNorm (p.1 - p.2) / 2) ^ (-α) ≤ 2 * euclideanNorm (p.1 - p.2) ^ (-α) := by
        have h2a : (2 : ℝ) ^ α ≤ 2 := by
          simpa using Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith : α ≤ 1)
        calc (euclideanNorm (p.1 - p.2) / 2) ^ (-α)
          _ = euclideanNorm (p.1 - p.2) ^ (-α) * (2 : ℝ) ^ α := by
              rw [div_eq_mul_inv, Real.mul_rpow hρ.le (by positivity), Real.inv_rpow zero_le_two,
                ← Real.rpow_neg zero_le_two, neg_neg]
          _ ≤ 2 * euclideanNorm (p.1 - p.2) ^ (-α) := by
              nlinarith [mul_le_mul_of_nonneg_left h2a (Real.rpow_nonneg hρ.le (-α))]
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), hint_eq,
        Real.norm_eq_abs, abs_mul (ψ p.1 * φ p.2), abkRieszKernel, abs_of_nonneg (Real.rpow_nonneg hρ.le _)]
      dsimp [C]
      calc |ψ p.1 * φ p.2| * ((2 : ℝ) ^ d * ((euclideanNorm (p.1 - p.2) / 2) ^ (-α) / α))
        _ ≤ |ψ p.1 * φ p.2| * ((2 : ℝ) ^ d * (2 * euclideanNorm (p.1 - p.2) ^ (-α) / α)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right hdiv hα_pos.le) (by positivity)) (abs_nonneg _)
        _ = _ := by ring
  have hF_meas : AEStronglyMeasurable F ν := by
    let S : Set ((Vec d × Vec d) × ℝ) := {q | 0 < q.2}
    have hS : MeasurableSet S := measurableSet_lt measurable_const continuous_snd.measurable
    have hself : AEStronglyMeasurable
        (fun q : (Vec d × Vec d) × ℝ => abkScaledCutoffSelfConvolution ζ q.2 (q.1.1 - q.1.2)) ν := by
      have hi : StronglyMeasurable (fun qy : ((Vec d × Vec d) × ℝ) × Vec d =>
          abkScaledCutoff ζ qy.1.2 qy.2 * abkScaledCutoff ζ qy.1.2 (qy.1.1.1 - qy.1.1.2 - qy.2)) := by
        unfold abkScaledCutoff
        exact (ζ.continuous.measurable.comp (by fun_prop)).stronglyMeasurable.mul
          (ζ.continuous.measurable.comp (by fun_prop)).stronglyMeasurable
      simpa [abkScaledCutoffSelfConvolution, ν] using (hi.integral_prod_right' (ν := volume)).aestronglyMeasurable
    have hpos : AEStronglyMeasurable (fun q : (Vec d × Vec d) × ℝ =>
        ψ q.1.1 * φ q.1.2 * (q.2 ^ (-(1 + (d : ℝ) + α)) * abkScaledCutoffSelfConvolution ζ q.2 (q.1.1 - q.1.2)))
        (ν.restrict S) :=
      (((ψ.continuous.comp continuous_fst.fst).mul (φ.continuous.comp continuous_fst.snd)).aestronglyMeasurable.restrict).mul
        (((continuous_snd.measurable.pow_const _).aestronglyMeasurable.restrict).mul hself.restrict)
    exact (AEStronglyMeasurable.piecewise hS hpos aestronglyMeasurable_const).congr
      (ae_of_all _ fun q => by by_cases hq : q ∈ S <;> rfl)
  have hF_int : Integrable F ν :=
    hG_int.mono' hF_meas (ae_of_all _ fun q => norm_pairInt_le_pairMaj q.1)
  have hscale : (∫ r : ℝ, abkRegularizedScaleProductSection ζ ψ φ α r) =
      ∫ r : ℝ, ∫ p : Vec d × Vec d, F (p, r) ∂μ := by
    refine integral_congr_ae (hF_int.prod_left_ae.mono fun r hp_int => ?_)
    dsimp only
    by_cases hr : 0 < r
    · simp only [abkRegularizedScaleProductSection, hr, ↓reduceIte]
      rw [integral_prod _ hp_int,
        abkScaleProductSection_eq_selfConvolution_integral_of_pos ζ ψ φ hr, ← mul_assoc, ← Real.rpow_add hr,
        show -α + -((d : ℝ) + 1) = -(1 + (d : ℝ) + α) by ring, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      dsimp only
      rw [← integral_const_mul, ← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun z => by simp [F, pairInt, hr]; ring)
    · simp [abkRegularizedScaleProductSection, F, pairInt, hr]
  have hinner (p : Vec d × Vec d) : (∫ r : ℝ, F (p, r)) = ψ p.1 * φ p.2 *
      ∫ r in Set.Ioi (0 : ℝ), r ^ (-(1 + (d : ℝ) + α)) * abkScaledCutoffSelfConvolution ζ r (p.1 - p.2) := by
    change (∫ r : ℝ, (Set.Ioi (0 : ℝ)).indicator (fun r : ℝ =>
      ψ p.1 * φ p.2 * (r ^ (-(1 + (d : ℝ) + α)) * abkScaledCutoffSelfConvolution ζ r (p.1 - p.2))) r) = _
    rw [integral_indicator measurableSet_Ioi, integral_const_mul]
  rw [hscale, (integral_integral_swap hF_int).symm]
  simp_rw [hinner]
  have hint_p : Integrable (fun p : Vec d × Vec d => ψ p.1 * φ p.2 *
      ∫ r in Set.Ioi (0 : ℝ), r ^ (-(1 + (d : ℝ) + α)) * abkScaledCutoffSelfConvolution ζ r (p.1 - p.2)) μ := by
    simpa [hinner] using hF_int.integral_prod_left
  rw [integral_prod _ hint_p]
  have hleft : (∫ x : Vec d, ∫ z : Vec d, ψ x * φ z *
        ∫ r in Set.Ioi (0 : ℝ), r ^ (-(1 + (d : ℝ) + α)) * abkScaledCutoffSelfConvolution ζ r (x - z)) =
      ∫ x : Vec d, ψ x * ∫ z : Vec d, φ z *
        ∫ r in Set.Ioi (0 : ℝ), r ^ (-(1 + (d : ℝ) + α)) * abkScaledCutoffSelfConvolution ζ r (x - z) :=
    integral_congr_ae (ae_of_all _ fun x => by
      dsimp only; rw [← integral_const_mul]; exact integral_congr_ae (ae_of_all _ fun z => by dsimp only; ring))
  have hR_iter : abkRieszPairing ψ φ α =
      ∫ x : Vec d, ψ x * ∫ z : Vec d, φ z * euclideanNorm (x - z) ^ (-α) := by
    unfold abkRieszPairing
    rw [abkKernelPairing_eq_integral_integral ψ φ (abkRieszKernel α) hR]
    exact integral_congr_ae (ae_of_all _ fun x => by
      dsimp only; rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun z => by dsimp only; simp [abkRieszKernel]; ring))
  rw [hleft, integral_integral_abkPowerDecomposition_kernel_eq_riesz_pairing hd ζ ψ φ α,
    ← hR_iter, abkCenteredRieszDifferencePairing_eq_rieszPairing ψ φ α hR]

end GaussianFields

end
