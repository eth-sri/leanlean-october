/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.RealSecondParent
public import DOZZ.Hypergeom.Planar.TaylorIntegral
public import DOZZ.Hypergeom.Planar.DifferenceIntegral
public import DOZZ.Hypergeom.Planar.RieszNormalization
public import DOZZ.Hypergeom.Planar.DerivativeIntegrable
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-! The pure Wirtinger integral follows from the real second derivative and the mixed Riesz
convolution. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace DOZZ.Proofs

private noncomputable def planarRieszCoefficientReal (k β : ℝ) : ℝ :=
  ((k / 2) ^ 2 / ((2 + k - β) / 2) ^ 2) * Real.pi *
    (Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) * Real.Gamma ((β - k) / 2) /
      (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) * Real.Gamma (1 + (k - β) / 2)))

private noncomputable def planarWirtingerTargetReal (k β : ℝ) : ℝ :=
  ((2 + k - β) / 2) * ((2 + k - β) / 2 - 1) * planarRieszCoefficientReal k β


section
variable (k β : ℝ) (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2)
include hk hβ hβ₂

private theorem planarWirtinger_integral_at_one_from_parent (A : ℝ)
    (hA : (A : ℂ) = DOZZ.planarGaussConstant k β)
    (hsecond : (∫ u : ℂ, planarRealSecondDifferenceLimit k β u) = (2 + k - β) * (1 + k - β) * A) :
    (k / 2) * (k / 2 - 1) * (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u) =
      ((2 + k - β) / 2) * ((2 + k - β) / 2 - 1) * DOZZ.planarGaussConstant k β := by
  have planarRealSecondDifferenceLimit_decompose (u : ℂ) (hu0 : u ≠ 0) (hu1 : u ≠ 1) : planarRealSecondDifferenceLimit k β u =
        2 * ((k / 2) * (k / 2 - 1) * (DOZZ.planarWirtingerKernel k β 1 u).re +
          (k / 2) ^ 2 * DOZZ.planarMixedKernel k β 1 u) := by
    have hv : u - 1 ≠ 0 := sub_ne_zero.2 hu1
    have hs : 0 < ‖u - 1‖ := norm_pos_iff.2 hv
    have hW : (DOZZ.planarWirtingerKernel k β 1 u).re =
        ‖u‖ ^ (-β) * (((‖u - 1‖ ^ k : ℝ) : ℂ) / (u - 1) ^ 2).re := by
      rw [DOZZ.planarWirtingerKernel, show (1 : ℂ) - u = -(u - 1) by ring, neg_sq,
        show (((‖u - 1‖ ^ k : ℝ) : ℂ) / ((u - 1) ^ 2 * ((‖u‖ ^ β : ℝ) : ℂ))) =
          (((‖u - 1‖ ^ k : ℝ) : ℂ) / (u - 1) ^ 2) / (‖u‖ ^ β : ℝ) by
            field_simp [pow_ne_zero 2 hv, (Real.rpow_pos_of_pos (norm_pos_iff.2 hu0) β).ne'],
        Complex.div_ofReal_re, Real.rpow_neg (norm_nonneg u)]
      ring
    have hsqre : ((u - 1) ^ 2).re = 2 * (u - 1).re ^ 2 - ‖u - 1‖ ^ 2 := by
      rw [pow_two, Complex.mul_re]
      have hnorm : ‖u - 1‖ ^ 2 = (u - 1).re ^ 2 + (u - 1).im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
      linear_combination hnorm
    have hsqnorm : Complex.normSq ((u - 1) ^ 2) = ‖u - 1‖ ^ 4 := by
      rw [pow_two, Complex.normSq_mul, Complex.normSq_eq_norm_sq]; ring
    have hRe : (((‖u - 1‖ ^ k : ℝ) : ℂ) / (u - 1) ^ 2).re =
        ‖u - 1‖ ^ (k - 4) * (2 * (u - 1).re ^ 2 - ‖u - 1‖ ^ 2) := by
      rw [Complex.div_re, hsqre, hsqnorm]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
      rw [show ‖u - 1‖ ^ k * (2 * (u - 1).re ^ 2 - ‖u - 1‖ ^ 2) / ‖u - 1‖ ^ 4 =
        (‖u - 1‖ ^ k / ‖u - 1‖ ^ ((4 : ℕ) : ℝ)) * (2 * (u - 1).re ^ 2 - ‖u - 1‖ ^ 2) by
          rw [Real.rpow_natCast]; ring, ← Real.rpow_sub hs,
        show k - ((4 : ℕ) : ℝ) = k - 4 by norm_num]
    have hM : DOZZ.planarMixedKernel k β 1 u = ‖u‖ ^ (-β) * (‖u - 1‖ ^ (k - 4) * ‖u - 1‖ ^ 2) := by
      rw [DOZZ.planarMixedKernel, div_eq_mul_inv, Real.rpow_neg (norm_nonneg u),
        ← Real.rpow_natCast ‖u - 1‖ 2, ← Real.rpow_add hs,
        show k - 4 + ((2 : ℕ) : ℝ) = k - 2 by push_cast; ring, mul_comm]
    have hpow1 : (‖u - 1‖ ^ (2 : ℕ)) ^ (k / 2 - 2) = ‖u - 1‖ ^ (k - 4) := by
      rw [← Real.rpow_natCast ‖u - 1‖ 2, ← Real.rpow_mul hs.le]; congr 1; push_cast; ring
    have hpow2 : (‖u - 1‖ ^ (2 : ℕ)) ^ (k / 2 - 1) = ‖u - 1‖ ^ (k - 4) * ‖u - 1‖ ^ 2 := by
      rw [← Real.rpow_natCast ‖u - 1‖ 2, ← Real.rpow_mul hs.le, ← Real.rpow_add hs]; congr 1; push_cast; ring
    rw [planarRealSecondDifferenceLimit, hW, hRe, hM, hpow1, hpow2]
    ring
  let W := DOZZ.planarWirtingerKernel k β 1
  let M := DOZZ.planarMixedKernel k β 1
  have hWInt : Integrable W volume :=
    (integrable_planarWirtingerKernel_iff k β hk 1 (by norm_num)).2 ⟨hβ, hβ₂⟩
  have hMData := planar_mixed_integral k β hk hβ hβ₂ 1 (by norm_num)
  have hdecomp : (∫ u : ℂ, planarRealSecondDifferenceLimit k β u) =
      2 * ((k / 2) * (k / 2 - 1) * (∫ u, (W u).re) + (k / 2) ^ 2 * ∫ u, M u) := by
    refine (integral_congr_ae
      (g := fun u => 2 * ((k / 2) * (k / 2 - 1) * (W u).re + (k / 2) ^ 2 * M u)) ?_).trans ?_
    · filter_upwards [Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume 1] with u hu0 hu1
      exact planarRealSecondDifferenceLimit_decompose u hu0 hu1
    · have hWI : Integrable (fun u => (k / 2) * (k / 2 - 1) * (W u).re) volume := hWInt.re.const_mul _
      rw [integral_const_mul, integral_add hWI (hMData.1.const_mul _),
        integral_const_mul, integral_const_mul]
  have hrefl (u : ℂ) : W (star u) = star (W u) := by
    have hnum : ‖star u - (1 : ℂ)‖ = ‖u - 1‖ := by rw [← norm_star (u - 1)]; simp
    dsimp only [W]
    rw [DOZZ.planarWirtingerKernel, DOZZ.planarWirtingerKernel, hnum]; simp
  have hWself : star (∫ u, W u) = ∫ u, W u := by
    calc star (∫ u, W u)
      _ = ∫ u, star (W u) := by simpa only [starRingEnd_apply] using (integral_conj (f := W)).symm
      _ = ∫ u, W (Complex.conjLIE u) := integral_congr_ae (Eventually.of_forall fun u => (hrefl u).symm)
      _ = ∫ u, W u := (LinearIsometryEquiv.measurePreserving Complex.conjLIE).integral_comp
          Complex.conjLIE.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding W
  have hWreal : (∫ u, W u) = ((∫ u, (W u).re : ℝ) : ℂ) :=
    (Complex.conj_eq_iff_re.mp hWself).symm.trans (congrArg Complex.ofReal (integral_re hWInt).symm)
  have hMval : (((k / 2) ^ 2 * ∫ u, M u : ℝ) : ℂ) =
      (((2 + k - β : ℂ) / 2) ^ 2) * DOZZ.planarGaussConstant k β := by
    simpa [M, norm_one, Real.one_rpow] using hMData.2
  have hbal : (((2 + k - β) * (1 + k - β) * A : ℝ) : ℂ) =
      ((2 * ((k / 2) * (k / 2 - 1) * (∫ u, (W u).re) + (k / 2) ^ 2 * ∫ u, M u) : ℝ) : ℂ) :=
    congrArg Complex.ofReal (hsecond.symm.trans hdecomp)
  rw [show (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u) = ∫ u, W u from rfl, hWreal]
  push_cast at hbal hMval ⊢
  rw [hA] at hbal
  linear_combination (-1 / 2 : ℂ) * hbal - hMval


private theorem planarWirtingerTargetReal_eq :
    ((2 + k - β) / 2) * ((2 + k - β) / 2 - 1) * DOZZ.planarGaussConstant k β =
      (planarWirtingerTargetReal k β : ℂ) := by
  rw [← (by simpa [planarRieszCoefficientReal] using
    positive_riesz_coefficient_eq_planarGaussConstant k β hk hβ hβ₂ :
    (planarRieszCoefficientReal k β : ℂ) = DOZZ.planarGaussConstant k β), planarWirtingerTargetReal]
  push_cast; ring

private theorem planarWirtinger_integral_at_one_value_all :
    (k / 2) * (k / 2 - 1) * (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u) =
      ((2 + k - β) / 2) * ((2 + k - β) / 2 - 1) * DOZZ.planarGaussConstant k β := by
  have planarWirtinger_integral_at_one_value (β : ℝ) (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) (hβne : β ≠ k + 1) : (k / 2) * (k / 2 - 1) * (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u) =
        ((2 + k - β) / 2) * ((2 + k - β) / 2 - 1) * DOZZ.planarGaussConstant k β := by
    rcases lt_or_gt_of_ne hβne with hT | hD
    · exact planarWirtinger_integral_at_one_from_parent k β hk hβ hβ₂ _
        (by simpa [norm_one, Real.one_rpow, integral_complex_ofReal] using
          ((planar_taylor_integral k β hk hβ hβ₂ hT) 1).2)
        (planarTaylor_real_second_derivative_relation k β hk hβ hβ₂ hT)
    · exact planarWirtinger_integral_at_one_from_parent k β hk hβ hβ₂ _
        (by simpa [norm_one, Real.one_rpow, integral_complex_ofReal] using
          ((planar_difference_integral k β hk hD hβ₂) 1).2)
        (planarDifference_real_second_derivative_relation k β hk (by linarith) hβ₂ hD)
  by_cases hβeq : β = k + 1
  · subst hβeq
    have hk1 : k < 1 := by linarith
    have hDCT : Tendsto (fun b : ℝ => ∫ u : ℂ, DOZZ.planarWirtingerKernel k b 1 u)
        (𝓝 (k + 1)) (𝓝 (∫ u : ℂ, DOZZ.planarWirtingerKernel k (k + 1) 1 u)) := by
      let δ := (1 - k) / 2
      have : 0 < δ := by dsimp [δ]; linarith
      let βlo := k + 1 - δ
      let βhi := k + 1 + δ
      let B : ℂ → ℝ := fun u => ‖u‖ ^ (-βlo) * ‖u - 1‖ ^ (k - 2) + ‖u‖ ^ (-βhi) * ‖u - 1‖ ^ (k - 2)
      have hparam : ∀ᶠ b : ℝ in 𝓝 (k + 1), βlo < b ∧ b < βhi :=
        Ioo_mem_nhds (by dsimp [βlo]; linarith) (by dsimp [βhi]; linarith)
      have := positive_riesz_convolution_integrable k βlo hk (by dsimp [βlo, δ]; linarith)
        (by dsimp [βlo, δ]; linarith) 1 (by norm_num)
      have := positive_riesz_convolution_integrable k βhi hk (by dsimp [βhi, δ]; linarith)
        (by dsimp [βhi, δ]; linarith) 1 (by norm_num)
      refine tendsto_integral_filter_of_dominated_convergence B
        (hparam.mono fun b hb => ((integrable_planarWirtingerKernel_iff k b hk 1 (by norm_num)).2
          ⟨by dsimp [βlo, δ] at hb; linarith, by dsimp [βhi, δ] at hb; linarith⟩).aestronglyMeasurable)
        (hparam.mono fun b hb => ?_) (by fun_prop) ?_
      · filter_upwards [Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume 1] with u hu0 hu1
        rw [norm_planarWirtingerKernel_eq k b 1 u hu0 hu1, div_eq_mul_inv,
          ← Real.rpow_neg (norm_nonneg u), mul_comm]
        have hs0 : 0 ≤ ‖u - 1‖ ^ (k - 2) := Real.rpow_nonneg (norm_nonneg _) _
        by_cases hle : ‖u‖ ≤ 1
        · exact (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge
            (norm_pos_iff.2 hu0) hle (by linarith)) hs0).trans
            (le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg (norm_nonneg u) _) hs0))
        · exact (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le
            (le_of_not_ge hle) (by linarith)) hs0).trans
            (le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg (norm_nonneg u) _) hs0))
      · filter_upwards [Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume 1] with u hu0 hu1
        refine tendsto_const_nhds.div (tendsto_const_nhds.mul
          (Complex.continuous_ofReal.continuousAt.tendsto.comp
            (Real.continuousAt_const_rpow (norm_ne_zero_iff.2 hu0)).tendsto))
          (mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.2 (Ne.symm hu1)))
            (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (norm_pos_iff.2 hu0) _).ne'))
    have cΓ (g : ℝ → ℝ) (hg : ContinuousAt g (k + 1)) (hp : 0 < g (k + 1)) :=
      (Real.differentiableAt_Gamma fun m => by linarith [Nat.cast_nonneg (α := ℝ) m]).continuousAt.comp hg
    have hcont : ContinuousAt (planarWirtingerTargetReal k) (k + 1) := by
      unfold planarWirtingerTargetReal planarRieszCoefficientReal
      have h1 := cΓ (fun b => 1 - b / 2) (by fun_prop) (by linarith)
      have h2 := cΓ (fun b => (b - k) / 2) (by fun_prop) (by norm_num)
      have h3 := cΓ (fun b => b / 2) (by fun_prop) (by linarith)
      have h4 := cΓ (fun b => 1 + (k - b) / 2) (by fun_prop) (by norm_num)
      have hD : Real.Gamma ((k + 1) / 2) * Real.Gamma (1 - k / 2) *
          Real.Gamma (1 + (k - (k + 1)) / 2) ≠ 0 :=
        (mul_pos (mul_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.Gamma_pos_of_pos (by linarith)))
          (Real.Gamma_pos_of_pos (by norm_num))).ne'
      have hq : ((2 + k - (k + 1)) / 2) ^ 2 ≠ 0 := by linarith
      have hqC : ContinuousAt (fun b => ((2 + k - b) / 2) ^ 2) (k + 1) := by fun_prop
      exact (((by fun_prop : ContinuousAt (fun b => (2 + k - b) / 2 * ((2 + k - b) / 2 - 1)) (k + 1))).mul
        (((continuousAt_const.div hqC hq).mul continuousAt_const).mul
          (((h1.mul continuousAt_const).mul h2).div ((h3.mul continuousAt_const).mul h4) hD)))
    let L : ℝ → ℂ := fun b => (k / 2 : ℂ) * ((k : ℂ) / 2 - 1) * ∫ u, DOZZ.planarWirtingerKernel k b 1 u
    let R : ℝ → ℂ := fun b => (planarWirtingerTargetReal k b : ℂ)
    have hL : Tendsto L (𝓝[≠] (k + 1)) (𝓝 (L (k + 1))) :=
      (tendsto_const_nhds.mul hDCT).mono_left nhdsWithin_le_nhds
    have hR : Tendsto R (𝓝[≠] (k + 1)) (𝓝 (R (k + 1))) :=
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hcont.tendsto).mono_left nhdsWithin_le_nhds
    have heq : L =ᶠ[𝓝[≠] (k + 1)] R := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds
        (Ioo_mem_nhds (show k < k + 1 by linarith) (show k + 1 < 2 by linarith)),
        self_mem_nhdsWithin] with b hb hbe
      exact (planarWirtinger_integral_at_one_value b hk hb.1 hb.2 hbe).trans
        (planarWirtingerTargetReal_eq k b hk hb.1 hb.2)
    exact (tendsto_nhds_unique (hL.congr' heq) hR).trans
      (planarWirtingerTargetReal_eq k (k + 1) hk (by linarith) (by linarith)).symm
  · exact planarWirtinger_integral_at_one_value β hk hβ hβ₂ hβeq

theorem planar_wirtinger_integral :
    ∀ z : ℂ, z ≠ 0 → Integrable (DOZZ.planarWirtingerKernel k β z) volume ∧
      (k / 2 : ℝ) * (k / 2 - 1 : ℝ) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k β z u) =
        ((2 + k - β) / 2 : ℝ) * ((2 + k - β) / 2 - 1 : ℝ) *
          (‖z‖ ^ (2 + k - β) : ℝ) / z ^ 2 *
            DOZZ.planarGaussConstant k β := by
  intro z hz
  refine ⟨(integrable_planarWirtingerKernel_iff k β hk z hz).2 ⟨hβ, hβ₂⟩, ?_⟩
  let r : ℝ := ‖z‖
  have hr : 0 < r := norm_pos_iff.2 hz
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  let ξ := z / (r : ℂ)
  have hξ : ‖ξ‖ = 1 := by simp [ξ, r, div_self hr.ne']
  have hzv (v : ℂ) : ξ * ((r : ℂ) * v) = z * v := by dsimp [ξ]; field_simp [hrC]
  have hpt (v : ℂ) : DOZZ.planarWirtingerKernel k β z (z * v) =
      ((r ^ (k - β) : ℝ) / z ^ 2) * DOZZ.planarWirtingerKernel k β 1 v := by
    by_cases hv0 : v = 0
    · subst hv0; simp [DOZZ.planarWirtingerKernel, Real.zero_rpow (hk.trans hβ).ne']
    by_cases hv1 : v = 1
    · subst hv1; simp [DOZZ.planarWirtingerKernel, Real.zero_rpow hk.ne']
    rw [DOZZ.planarWirtingerKernel, DOZZ.planarWirtingerKernel,
      show z * v - z = z * (v - 1) by ring, show z - z * v = z * (1 - v) by ring,
      norm_mul, norm_mul, mul_pow, show ‖z‖ = r from rfl,
      Real.mul_rpow hr.le (norm_nonneg _), Real.mul_rpow hr.le (norm_nonneg _)]
    have hrk : r ^ k = r ^ (k - β) * r ^ β := by
      rw [← Real.rpow_add hr]; congr 1; ring
    have hv1' : (1 : ℂ) - v ≠ 0 := sub_ne_zero.2 (Ne.symm hv1)
    push_cast
    field_simp [pow_ne_zero 2 hz, pow_ne_zero 2 hv1', Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hr β).ne', Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (norm_pos_iff.2 hv0) β).ne']
    rw [hrk]; push_cast; ring
  let g : ℂ → ℂ := fun u => DOZZ.planarWirtingerKernel k β z (ξ * u)
  let c : Circle := ⟨ξ, by simpa [Submonoid.unitSphere] using hξ⟩
  have hrot : ∫ u, g u = ∫ u, DOZZ.planarWirtingerKernel k β z u := by
    simpa only [g, rotation_apply] using
      (LinearIsometryEquiv.measurePreserving (rotation c)).integral_comp
        (rotation c).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
        (DOZZ.planarWirtingerKernel k β z)
  have hsc : ∫ v, g (r • v) = (((r ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) * ∫ u, DOZZ.planarWirtingerKernel k β z u := by
    rw [← hrot]
    simpa only [Complex.finrank_real_complex, Complex.real_smul] using
      Measure.integral_comp_smul_of_nonneg volume g r (hR := hr.le)
  have hlhs : ∫ v, g (r • v) =
      ((r ^ (k - β) : ℝ) / z ^ 2) * ∫ v, DOZZ.planarWirtingerKernel k β 1 v := by
    have : (fun v => g (r • v)) = fun v => ((r ^ (k - β) : ℝ) / z ^ 2) *
        DOZZ.planarWirtingerKernel k β 1 v := by ext v; simp only [g, Complex.real_smul, hzv, hpt]
    rw [this, integral_const_mul]
  have hscale : ∫ u, DOZZ.planarWirtingerKernel k β z u =
      ((r ^ (2 + k - β) : ℝ) / z ^ 2) * ∫ v, DOZZ.planarWirtingerKernel k β 1 v := by
    have hmul := congrArg (((r ^ 2 : ℝ) : ℂ) * ·) (hsc.symm.trans hlhs)
    have hrpow : ((r ^ 2 : ℝ) : ℂ) * (r ^ (k - β) : ℝ) = (r ^ (2 + k - β) : ℝ) := by
      rw [← Complex.ofReal_mul, ← Real.rpow_natCast r 2, ← Real.rpow_add hr]; congr 2; ring
    have h1 : ((r ^ 2 : ℝ) : ℂ) * ((((r ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) * ∫ u, DOZZ.planarWirtingerKernel k β z u) =
        ∫ u, DOZZ.planarWirtingerKernel k β z u := by
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (pow_ne_zero 2 hr.ne'),
        Complex.ofReal_one, one_mul]
    rw [h1] at hmul
    rw [hmul, show ((r ^ 2 : ℝ) : ℂ) * (((r ^ (k - β) : ℝ) / z ^ 2) *
        ∫ v, DOZZ.planarWirtingerKernel k β 1 v) =
      ((((r ^ 2 : ℝ) : ℂ) * (r ^ (k - β) : ℝ)) / z ^ 2) *
        ∫ v, DOZZ.planarWirtingerKernel k β 1 v by ring, hrpow]
  rw [hscale, show ((k / 2 : ℝ) : ℂ) * ((k / 2 - 1 : ℝ) : ℂ) *
      (((r ^ (2 + k - β) : ℝ) / z ^ 2) * ∫ v, DOZZ.planarWirtingerKernel k β 1 v) =
    ((r ^ (2 + k - β) : ℝ) / z ^ 2) * ((k / 2 : ℂ) * ((k : ℂ) / 2 - 1) *
      ∫ v, DOZZ.planarWirtingerKernel k β 1 v) by push_cast; ring,
    planarWirtinger_integral_at_one_value_all k β hk hβ hβ₂]
  push_cast; ring


end
end DOZZ.Proofs
