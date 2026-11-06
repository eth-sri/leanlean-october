/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedOuter.RootedFreezing
public import DOZZ.FourPoint.TaylorOneRootIdentity
public import DOZZ.FourPoint.TaylorRadialBall
import Mathlib.Tactic

/-! # The deleted-disk error at the reflected freezing power -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs


/-- Rooting and the local freezing estimate give the full deleted-disk power `κ+δ`. -/
theorem reflected_deleted_disk_weight_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα₁ : α₁ < Q γ)
    (hreflect : Q γ - α₁ < γ / 2) (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ r : ℝ, 0 < r → r < ε₀ →
      (∫⁻ ω, (∫⁻ x in Metric.ball (0 : ℂ) r,
          ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x) ∂M ω) *
        (reflectedRetainedZeroMass γ α₁ α₂ α₃ r (M ω)) ^
          (-((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 1)) ∂P) ≤
      ENNReal.ofReal (C * r ^
        (γ * (Q γ - α₁) + (α₁ + γ / 2 - Q γ) ^ 2 / 2)) := by
  have reflected_zero_kernel_local_upper x (hx : ‖x‖ < 1 / 2) : gammaHalfKernel γ α₁ α₂ α₃ 0 x ≤ (2 : ℝ) ^ |γ * α₂| * ‖x‖ ^ (γ * (Q γ - α₁) - 2) := by
    by_cases hx0 : x = 0
    · subst x
      have hk : γ ^ 2 / 2 ≠ 0 := (div_pos (sq_pos_of_pos hγ) (by norm_num)).ne'
      simp only [gammaHalfKernel, sub_zero, norm_zero, Real.zero_rpow hk, zero_mul, zero_div]
      positivity
    have hn := norm_pos_iff.mpr hx0
    have hd1 : (2 : ℝ)⁻¹ ≤ ‖x - 1‖ := by
      have hh := norm_sub_norm_le (1 : ℂ) x
      rw [norm_one, norm_sub_rev] at hh
      norm_num at hh ⊢
      linarith only [hh, hx]
    have hd2 : ‖x - 1‖ ≤ 2 := by
      have hh := norm_sub_le x (1 : ℂ)
      rw [norm_one] at hh
      linarith only [hh, hx]
    have hd := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2⁻¹) hd1
    have he : -(γ * (α₁ - γ / 2)) = γ * (Q γ - α₁) - 2 := by
      unfold Q
      field_simp
      ring
    rw [reflected_zero_kernel_weight γ α₁ α₂ α₃ x hx0 (sub_ne_zero.mp (norm_pos_iff.mp hd))]
    unfold normPlus
    rw [max_eq_left (by linarith only [hx] : ‖x‖ ≤ 1), Real.one_rpow,
      div_eq_mul_inv, one_mul, mul_inv, ← Real.rpow_neg hn.le, ← Real.rpow_neg hd.le, he]
    exact (mul_le_mul_of_nonneg_left (by simpa only [neg_mul, abs_neg] using (coulombWeight_rpow_le (L := 2) (y := ‖x - 1‖) (by norm_num) hd1 hd2 (-γ * α₂))) (Real.rpow_nonneg hn.le _)).trans_eq (mul_comm _ _)
  let κ : ℝ := γ * (Q γ - α₁)
  let δ : ℝ := (α₁ + γ / 2 - Q γ) ^ 2 / 2
  let w : ℝ := (2 : ℝ) ^ |γ * α₂|
  have hw : 0 < w := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨Cr, εr, hCr, hεr, hb⟩ := reflected_retainedZero_rooted_inverse_freezing
    P X M γ α₁ α₂ α₃ hγ hγ₂ hα₁ hreflect hs hX hM
  obtain ⟨Cd, hCd, hdb⟩ := planar_radial_ball_bound (κ - 2) (by linarith only [(mul_pos hγ (sub_pos.mpr hα₁))])
  refine ⟨Cr * w * Cd, min εr (1 / 2), by positivity, lt_min hεr (by norm_num), ?_⟩
  intro r hr hr₀
  have hrh : r < 1 / 2 := (lt_min_iff.mp hr₀).2
  let B : Set ℂ := Metric.ball 0 r
  let f : ℂ → ℝ≥0∞ := B.indicator (fun x => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x))
  let G : Measure ℂ → ℝ≥0∞ := fun μ => (reflectedRetainedZeroMass γ α₁ α₂ α₃ r μ) ^ (-((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 1))
  have hB : MeasurableSet B := measurableSet_ball
  have hf : Measurable f := (ENNReal.measurable_ofReal.comp
    (reflected_gammaHalfKernel_measurable γ α₁ α₂ α₃ 0)).indicator hB
  have hft : ∀ x, f x ≠ ⊤ := by
    intro x
    by_cases hx : x ∈ B
    · simp only [f, indicator_of_mem hx]; exact ENNReal.ofReal_ne_top
    · simp only [f, indicator_of_notMem hx, ne_eq, ENNReal.zero_ne_top, not_false_eq_true]
  have hsp : (∫⁻ x, f x ∂gmcReferenceMeasure) ≤ ENNReal.ofReal (w * (Cd * r ^ κ)) := by
    rw [lintegral_indicator hB, gmcReferenceMeasure_restrict_unit_chart B hB (by
      intro x hx
      linarith only [(by simpa only [B, Metric.mem_ball, dist_zero_right] using hx), hrh])]
    calc
      _ ≤ ∫⁻ x in B, ENNReal.ofReal w * ENNReal.ofReal (‖x‖ ^ (κ - 2)) := by
        apply setLIntegral_mono' hB
        intro x hx
        rw [← ENNReal.ofReal_mul hw.le]
        apply ENNReal.ofReal_le_ofReal
        apply reflected_zero_kernel_local_upper
        exact (show ‖x‖ < r by simpa only [B, Metric.mem_ball, dist_zero_right] using hx).trans hrh
      _ = ENNReal.ofReal w * (∫⁻ x in B, ENNReal.ofReal (‖x‖ ^ (κ - 2))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal w * ENNReal.ofReal (Cd * r ^ κ) := by
        apply mul_le_mul' le_rfl
        simpa only [sub_zero, sub_add_cancel] using hdb 0 r hr
      _ = _ := (ENNReal.ofReal_mul hw.le).symm
  calc
    _ = ∫⁻ x, f x * (∫⁻ ω, G (gmcRootedMeasure γ x (M ω)) ∂P) ∂gmcReferenceMeasure := by
      simpa only [f, lintegral_indicator hB] using
        rooted_weight_identity P X hX γ hγ hγ₂ M hM f hf hft G ((reflected_retainedZero_measure_measurable γ α₁ α₂ α₃ r).pow_const _)
    _ ≤ ∫⁻ x, f x * ENNReal.ofReal (Cr * r ^ δ) ∂gmcReferenceMeasure := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ B
      · apply mul_le_mul' le_rfl
        apply hb r hr ((lt_min_iff.mp hr₀).1) x
        exact (show ‖x‖ < r by simpa only [B, Metric.mem_ball, dist_zero_right] using hx).le
      · simp only [f, indicator_of_notMem hx, zero_mul, le_refl]
    _ = ENNReal.ofReal (Cr * r ^ δ) * (∫⁻ x, f x ∂gmcReferenceMeasure) := by
      rw [lintegral_mul_const _ hf, mul_comm]
    _ ≤ ENNReal.ofReal (Cr * r ^ δ) * ENNReal.ofReal (w * (Cd * r ^ κ)) := mul_le_mul' le_rfl hsp
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ Cr * r ^ δ)]
      congr 1
      calc
        _ = (Cr * w * Cd) * (r ^ δ * r ^ κ) := by ring
        _ = _ := by rw [(show r ^ δ * r ^ κ = r ^ (κ + δ) by rw [← Real.rpow_add hr, add_comm])]

end DOZZ.Proofs
