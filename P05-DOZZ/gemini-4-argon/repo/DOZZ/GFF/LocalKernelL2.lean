/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.CovarianceAlgebra
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# DOZZ.GFF.LocalKernelL2

The logarithmic diagonal singularity is square integrable locally in the plane. This is the
analytic input for the local L² Schur bound used by the G5 construction.
-/

@[expose] public section

open MeasureTheory Set Metric

namespace DOZZ

/-- The square of the planar logarithmic singularity is integrable on every ball.

Near zero, `|log r| r^(1/4)` is bounded, so the square is dominated by a constant times
`r^(-1/2)`, which is locally integrable in dimension two. Away from zero the same domination
follows from the elementary logarithm-versus-power bound. -/
theorem integrable_log_norm_sq_on_ball R :
    IntegrableOn (fun z : ℂ => (Real.log ‖z‖) ^ 2) (ball (0 : ℂ) R) := by
  have hdecay : ∀ᵐ z ∂(volume : Measure ℂ).restrict (ball (0 : ℂ) R),
      ‖(Real.log ‖z‖) ^ 2‖ ≤ 16 * max R 1 * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    rw [mem_ball_zero_iff] at hz
    by_cases hzsmall : ‖z‖ ≤ 1
    · by_cases hzzero : ‖z‖ = 0
      · simp [hzzero]
      · have hzNe : z ≠ 0 := by
          intro hz'
          apply hzzero
          simp [hz']
        have hpos := norm_pos_iff.mpr hzNe
        have hmulAbs : |Real.log ‖z‖| * ‖z‖ ^ (1 / 4 : ℝ) ≤ 4 := by
          have hb' := (Real.abs_log_mul_self_rpow_lt ‖z‖ (1 / 4 : ℝ) hpos hzsmall (by norm_num : (0 : ℝ) < 1 / 4)).le
          rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hpos _)] at hb'
          norm_num at hb' ⊢
          exact hb'
        have hpow : (‖z‖ ^ (1 / 4 : ℝ)) ^ 2 = ‖z‖ ^ (1 / 2 : ℝ) := by
          rw [pow_two, ← Real.rpow_add hpos]
          congr 1
          norm_num
        have hmul : (Real.log ‖z‖) ^ 2 * ‖z‖ ^ (1 / 2 : ℝ) ≤ 16 := by
          have hs := (sq_le_sq₀
            (by positivity : 0 ≤ |Real.log ‖z‖| * ‖z‖ ^ (1 / 4 : ℝ))
            (by norm_num : (0 : ℝ) ≤ 4)).2 hmulAbs
          rw [mul_pow, sq_abs, hpow] at hs
          norm_num at hs
          exact hs
        have hsmall : (Real.log ‖z‖) ^ 2 ≤ 16 * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
          calc
            (Real.log ‖z‖) ^ 2 ≤ 16 / ‖z‖ ^ (1 / 2 : ℝ) :=
              (le_div_iff₀ (Real.rpow_pos_of_pos hpos _)).2 hmul
            _ = 16 * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
              rw [div_eq_mul_inv, Real.rpow_neg (norm_nonneg z)]
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hsmall.trans (mul_le_mul_of_nonneg_right
          (by nlinarith [le_max_right R 1])
          (Real.rpow_pos_of_pos hpos _).le)
    · have hpos : 0 < ‖z‖ :=
        (by norm_num : (0 : ℝ) < 1).trans (lt_of_not_ge hzsmall)
      have hl : Real.log ‖z‖ ≤ 4 * ‖z‖ ^ (1 / 4 : ℝ) := by
        have h := Real.log_le_rpow_div (norm_nonneg z)
          (by norm_num : (0 : ℝ) < 1 / 4)
        rw [div_eq_mul_inv, show (1 / 4 : ℝ)⁻¹ = 4 by norm_num] at h
        nlinarith
      have hpowmul : (‖z‖ ^ (1 / 4 : ℝ)) ^ 2 = ‖z‖ ^ (1 / 2 : ℝ) := by
        rw [pow_two, ← Real.rpow_add hpos]
        congr 1
        norm_num
      have hsq : (Real.log ‖z‖) ^ 2 ≤ 16 * ‖z‖ ^ (1 / 2 : ℝ) := by
        have hs := (sq_le_sq₀ (Real.log_nonneg (le_of_not_ge hzsmall))
          (by positivity : (0 : ℝ) ≤ 4 * ‖z‖ ^ (1 / 4 : ℝ))).2 hl
        rw [mul_pow, hpowmul] at hs
        nlinarith [hs]
      have hrootmul : ‖z‖ ^ (1 / 2 : ℝ) * ‖z‖ ^ (1 / 2 : ℝ) = ‖z‖ := by
        calc
          _ = ‖z‖ ^ (1 / 2 + 1 / 2 : ℝ) := by rw [← Real.rpow_add hpos]
          _ = ‖z‖ := by norm_num [Real.rpow_one]
      have hpow : ‖z‖ ^ (1 / 2 : ℝ) ≤ max R 1 * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
        calc
          ‖z‖ ^ (1 / 2 : ℝ) =
              ‖z‖ ^ (1 / 2 : ℝ) * ‖z‖ ^ (1 / 2 : ℝ) / ‖z‖ ^ (1 / 2 : ℝ) := by
            field_simp
          _ ≤ max R 1 / ‖z‖ ^ (1 / 2 : ℝ) := by
            exact div_le_div_of_nonneg_right (by rw [hrootmul]; exact (hz.le.trans (le_max_left R 1))) (Real.rpow_pos_of_pos hpos _).le
          _ = max R 1 * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
            rw [div_eq_mul_inv, Real.rpow_neg (norm_nonneg z)]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc
        (Real.log ‖z‖) ^ 2 ≤ 16 * ‖z‖ ^ (1 / 2 : ℝ) := hsq
        _ ≤ 16 * (max R 1 * ‖z‖ ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hpow (by norm_num)
        _ = 16 * max R 1 * ‖z‖ ^ (-(1 / 2 : ℝ)) := by ring
  exact integrableOn_ball_of_norm_le_rpow (by rw [Complex.finrank_real_complex]; norm_num) (show (1 / 2 : ℝ) < Module.finrank ℝ ℂ by rw [Complex.finrank_real_complex]; norm_num) hdecay ((Real.measurable_log.comp measurable_norm).pow_const 2 |>.aestronglyMeasurable)

private def subProdMap (p : ℂ × ℂ) : ℂ × ℂ := (p.1 - p.2, p.2)

private def invSubProdMap (p : ℂ × ℂ) : ℂ × ℂ := (p.1 + p.2, p.2)

/-- The square of the difference-log singularity is integrable on the product of two bounded
balls. The measure-preserving shear `(x,y) ↦ (x-y,y)` reduces this to the one-variable result. -/
theorem integrable_log_norm_sub_sq_on_pair_ball R :
    IntegrableOn (fun p : ℂ × ℂ => (Real.log ‖p.1 - p.2‖) ^ 2)
      (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R)
      ((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
  let B : Set ℂ := ball 0 R
  let A : Set ℂ := ball 0 (2 * R)
  let μ : Measure (ℂ × ℂ) := (volume : Measure ℂ).prod (volume : Measure ℂ)
  have : IsFiniteMeasure (volume.restrict B) :=
    (MeasureTheory.isFiniteMeasure_restrict).2 (show volume B < ⊤ by dsimp [B]; exact measure_ball_lt_top).ne
  have hsurj : Function.Surjective subProdMap := by
    intro p
    refine ⟨invSubProdMap p, ?_⟩
    ext <;> simp [subProdMap, invSubProdMap]
  let S := B ×ˢ B
  have himage : subProdMap '' S ⊆ A ×ˢ B := by
    rintro q ⟨p, hp, rfl⟩
    rcases hp with ⟨hx, hy⟩
    change p.1 - p.2 ∈ A ∧ p.2 ∈ B
    constructor
    · rw [mem_ball_zero_iff] at hx hy ⊢
      calc
        ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
        _ < R + R := add_lt_add hx hy
        _ = 2 * R := by ring
    · exact hy
  simpa [B, S, μ] using (by simpa only [(show (fun p : ℂ × ℂ => (Real.log ‖p.1‖) ^ 2) ∘ subProdMap = fun p : ℂ × ℂ => (Real.log ‖p.1 - p.2‖) ^ 2 by funext p; rfl)] using (((show MeasurePreserving subProdMap μ μ by dsimp [μ, subProdMap]; exact MeasureTheory.measurePreserving_sub_prod _ _).integrableOn_image (MeasurableEmbedding.of_measurable_inverse (show Measurable subProdMap by change Measurable (fun p : ℂ × ℂ => (p.1 - p.2, p.2)); exact (measurable_fst.sub measurable_snd).prodMk measurable_snd) (show MeasurableSet (Set.range subProdMap) by rw [(Set.range_eq_univ.mpr hsurj)]; exact MeasurableSet.univ) (show Measurable invSubProdMap by change Measurable (fun p : ℂ × ℂ => (p.1 + p.2, p.2)); exact (measurable_fst.add measurable_snd).prodMk measurable_snd) (by intro p; ext <;> simp [subProdMap, invSubProdMap]))).mp ((show IntegrableOn (fun p : ℂ × ℂ => (Real.log ‖p.1‖) ^ 2) (A ×ˢ B) μ by rw [IntegrableOn, ← Measure.prod_restrict]; exact (show IntegrableOn (fun z => (Real.log ‖z‖) ^ 2) A volume by simpa [A] using integrable_log_norm_sq_on_ball (2 * R)).comp_fst (volume.restrict B)).mono_set himage)))


/-- The full pinned covariance kernel is square integrable on every bounded product box. -/
theorem integrable_gffKernel_sq_on_pair_ball R :
    IntegrableOn (fun p : ℂ × ℂ => (gffKernel p.1 p.2) ^ 2)
      (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R)
      ((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
  have integrable_log_normPlus_sq_on_pair_ball : IntegrableOn (fun p : ℂ × ℂ => (Real.log (normPlus p.1)) ^ 2) (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R) ((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
    let B : Set ℂ := ball 0 R
    let μ : Measure (ℂ × ℂ) := (volume : Measure ℂ).prod (volume : Measure ℂ)
    have hcont : Continuous (fun z => Real.log (normPlus z)) := by
      apply Continuous.log
      · exact continuous_const.max continuous_norm
      · intro z
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖z‖))
    have : IsFiniteMeasure (volume.restrict B) :=
      (MeasureTheory.isFiniteMeasure_restrict).2 (show volume B < ⊤ by dsimp [B]; exact measure_ball_lt_top).ne
    simpa [B, μ] using (by rw [IntegrableOn, ← Measure.prod_restrict]; exact (show IntegrableOn (fun z => (Real.log (normPlus z)) ^ 2) B volume by exact (hcont.pow 2 |>.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) R)).mono_set Metric.ball_subset_closedBall).comp_fst (volume.restrict B))
  let B : Set ℂ := ball 0 R
  let μ : Measure (ℂ × ℂ) := (volume : Measure ℂ).prod (volume : Measure ℂ)
  have hmeas : AEStronglyMeasurable
      (fun p : ℂ × ℂ => (gffKernel p.1 p.2) ^ 2) (μ.restrict (B ×ˢ B)) := by
    apply (show Measurable (fun p : ℂ × ℂ => (gffKernel p.1 p.2) ^ 2) from ?_)
      |>.aestronglyMeasurable
    fun_prop [gffKernel, normPlus]
  have hkernel : IntegrableOn
      (fun p : ℂ × ℂ => (gffKernel p.1 p.2) ^ 2) (B ×ˢ B) μ := by
    rw [IntegrableOn]
    apply (show IntegrableOn (fun p : ℂ × ℂ => 3 * ((Real.log ‖p.1 - p.2‖) ^ 2 + (Real.log (normPlus p.1)) ^ 2 + (Real.log (normPlus p.2)) ^ 2)) (B ×ˢ B) μ by change Integrable (fun p : ℂ × ℂ => 3 * ((Real.log ‖p.1 - p.2‖) ^ 2 + (Real.log (normPlus p.1)) ^ 2 + (Real.log (normPlus p.2)) ^ 2)) (((volume : Measure ℂ).prod (volume : Measure ℂ)).restrict (B ×ˢ B)); simpa [B, μ, add_assoc] using ((integrable_log_norm_sub_sq_on_pair_ball R).add ((integrable_log_normPlus_sq_on_pair_ball).add (by simpa [B, μ, Function.comp_def, Prod.swap] using (integrable_log_normPlus_sq_on_pair_ball).swap))).const_mul 3).mono' hmeas
    filter_upwards with p
    let a := -Real.log ‖p.1 - p.2‖
    let b := Real.log (normPlus p.1)
    let c := Real.log (normPlus p.2)
    calc
      ‖(gffKernel p.1 p.2) ^ 2‖ = (a + b + c) ^ 2 := by
        rw [(show gffKernel p.1 p.2 = a + b + c by simp [a, b, c, gffKernel]), Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (a + b + c))]
      _ ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := (by nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)])
      _ = 3 * ((Real.log ‖p.1 - p.2‖) ^ 2 +
          (Real.log (normPlus p.1)) ^ 2 + (Real.log (normPlus p.2)) ^ 2) := by
        simp [a, b, c]
  simpa [B, μ] using hkernel


end DOZZ

end
