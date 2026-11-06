/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.KernelIntegrability
public import BergmanWeakType.Weighted.PolarPotential
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # The circular boundary-kernel normalizer -/

@[expose] public section

noncomputable section

open MeasureTheory Real
open scoped ENNReal

namespace BergmanWeakType

theorem integral_sin_rpow {α : ℝ} (hα : -1 < α) :
    (∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ α) =
      Real.sqrt Real.pi * Real.Gamma ((α + 1) / 2) / Real.Gamma (1 + α / 2) := by
  have hp : 0 ≤ Real.pi / 2 := by positivity
  have hhalf : (∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ α) =
      Real.sqrt Real.pi * Real.Gamma ((α + 1) / 2) / (2 * Real.Gamma (1 + α / 2)) := by
    have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (f := fun x ↦ Real.sin x ^ 2) (f' := fun x ↦ 2 * Real.sin x * Real.cos x)
      (g := fun t ↦ t ^ ((α - 1) / 2) * (1 - t) ^ (-(1 / 2 : ℝ))) (by fun_prop)
      (fun x _ ↦ by simpa [Pi.pow_apply] using! (Real.hasDerivAt_sin x).pow 2)
      (fun x hx ↦ by
        rw [min_eq_left hp, max_eq_right hp] at hx
        exact mul_nonneg (mul_nonneg (by norm_num)
          (Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le (by linarith [hx.2])))
          (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1], hx.2.le⟩))
    simp only [Real.sin_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Real.sin_pi_div_two, one_pow, Function.comp_def] at hsub
    have heq : (∫ x in (0 : ℝ)..Real.pi / 2,
        ((Real.sin x ^ 2) ^ ((α - 1) / 2) * (1 - Real.sin x ^ 2) ^ (-(1 / 2 : ℝ))) *
          (2 * Real.sin x * Real.cos x)) =
        2 * (∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ α) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr_Ioo_of_le hp fun x hx ↦ ?_
      have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2])
      have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1], hx.2⟩
      rw [show 1 - Real.sin x ^ 2 = Real.cos x ^ 2 by nlinarith [Real.sin_sq_add_cos_sq x],
        ← Real.rpow_natCast (Real.sin x) 2, ← Real.rpow_mul hs.le,
        ← Real.rpow_natCast (Real.cos x) 2, ← Real.rpow_mul hc.le]
      norm_num only [Nat.cast_ofNat]
      rw [show (2 : ℝ) * ((α - 1) / 2) = α - 1 by ring, Real.rpow_neg_one,
        show Real.sin x ^ (α - 1) * (Real.cos x)⁻¹ * (2 * Real.sin x * Real.cos x) =
          2 * (Real.sin x ^ (α - 1) * Real.sin x) * ((Real.cos x)⁻¹ * Real.cos x) by ring,
        ← Real.rpow_add_one hs.ne', sub_add_cancel, inv_mul_cancel₀ hc.ne', mul_one]
    have hbeta : (∫ x in (0 : ℝ)..1, x ^ ((α - 1) / 2) * (1 - x) ^ (-(1 / 2 : ℝ))) =
        Real.Gamma ((α + 1) / 2) * Real.sqrt Real.pi / Real.Gamma (1 + α / 2) := by
      apply Complex.ofReal_injective
      rw [← intervalIntegral.integral_ofReal, ← Real.Gamma_one_half_eq]
      have hb := Complex.betaIntegral_eq_Gamma_mul_div ((α + 1) / 2 : ℂ) (1 / 2 : ℂ)
        (by simp [ Complex.add_re, Complex.div_ofNat_re]; linarith) (by norm_num)
      have hb' : (((α + 1) / 2 : ℝ) : ℂ) = ((α + 1) / 2 : ℂ) := by push_cast; rfl
      have hb'' : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; rfl
      rw [← hb', ← hb'', ← Complex.ofReal_add,
        show (α + 1) / 2 + 1 / 2 = 1 + α / 2 by ring] at hb
      simp only [Complex.Gamma_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_div] at hb
      rw [← hb]
      refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun x hx ↦ ?_
      simp only [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
        Complex.ofReal_cpow (sub_nonneg.mpr hx.2.le), Complex.ofReal_sub, Complex.ofReal_one]
      congr <;> push_cast <;> ring
    rw [heq, hbeta] at hsub
    calc
      _ = (Real.Gamma ((α + 1) / 2) * Real.sqrt Real.pi / Real.Gamma (1 + α / 2)) / 2 := by
        linarith
      _ = _ := by ring
  have hh : IntervalIntegrable (fun x ↦ Real.sin x ^ α) volume 0 (Real.pi / 2) := by
    refine intervalIntegral.intervalIntegrable_of_integral_ne_zero (hhalf.trans_ne (ne_of_gt ?_))
    exact div_pos (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.Gamma_pos_of_pos (by linarith)))
      (mul_pos (by norm_num) (Real.Gamma_pos_of_pos (by linarith)))
  have hr : IntervalIntegrable (fun x ↦ Real.sin x ^ α) volume (Real.pi / 2) Real.pi := by
    simpa only [Real.sin_pi_sub, sub_zero, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring]
      using (hh.comp_sub_left Real.pi).symm
  have heq : (∫ x in Real.pi / 2..Real.pi, Real.sin x ^ α) =
      ∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ α := by
    conv_lhs => arg 1; intro x; rw [← Real.sin_pi_sub x]
    rw [intervalIntegral.integral_comp_sub_left (fun x ↦ Real.sin x ^ α), sub_self,
      show Real.pi - Real.pi / 2 = Real.pi / 2 by ring]
  rw [← intervalIntegral.integral_add_adjacent_intervals hh hr, heq, hhalf]
  ring

def circleDenominator (r x : ℝ) : ℝ := 1 + r ^ 2 - 2 * r * x

theorem circleDenominator_pos {r x : ℝ} (hr : |r| < 1) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 < circleDenominator r x := by
  rcases abs_lt.mp hr with ⟨hr₁, hr₂⟩
  unfold circleDenominator
  nlinarith [mul_nonneg (sq_nonneg (1 - r)) (by linarith [hx.1] : 0 ≤ 1 + x),
    mul_nonneg (sq_nonneg (1 + r)) (by linarith [hx.2] : 0 ≤ 1 - x),
    sq_pos_of_pos (by linarith : 0 < 1 - r), sq_pos_of_pos (by linarith : 0 < 1 + r)]

/-- Circular mean of the positive boundary kernel at radial coordinate `r`. -/
def normalizer (α r : ℝ) : ℝ :=
  Real.circleAverage (fun ζ : ℂ ↦ ‖1 - (r : ℂ) * ζ‖ ^ (-(α + 2))) 0 1

theorem normalizer_eq_circleAverage_radius (α r : ℝ) :
    normalizer α r = Real.circleAverage (fun z : ℂ ↦ ‖1 - z‖ ^ (-(α + 2))) 0 r := by
  simpa [normalizer] using
    (Real.circleAverage_eq_circleAverage_zero_one
      (f := fun z : ℂ ↦ ‖1 - z‖ ^ (-(α + 2))) (c := 0) (R := r)).symm

@[simp] theorem normalizer_zero (α : ℝ) : normalizer α 0 = 1 := by
  simp [normalizer, Real.circleAverage_const]

theorem normalizer_nonneg (α r : ℝ) : 0 ≤ normalizer α r :=
  Real.circleAverage_nonneg_of_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _

theorem continuousOn_boundaryKernel_norm {s : Set ℂ} (p : ℝ) (hs : ∀ z ∈ s, ‖z‖ < 1) :
    ContinuousOn (fun z : ℂ ↦ ‖1 - z‖ ^ p) s :=
  (continuous_const.sub continuous_id).norm.continuousOn.rpow_const fun z hz ↦
    Or.inl (norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun h ↦ by
      change (1 : ℂ) = z at h; have hz' := hs z hz; simp [← h] at hz'))

theorem continuousOn_normalizer (α : ℝ) : ContinuousOn (normalizer α) (Set.Ico 0 1) := by
  change ContinuousOn (fun r ↦ normalizer α r) (Set.Ico 0 1)
  simp_rw [normalizer_eq_circleAverage_radius]
  exact Real.ContinuousOn.circleAverage
    (continuousOn_boundaryKernel_norm _ fun _ hz ↦ by simpa using hz.2)
    fun _ hr ↦ hr.1

theorem normalizer_pos {α r : ℝ} (hα : -1 < α) (hr : |r| < 1) :
    0 < normalizer α r := by
  refine (Real.rpow_pos_of_pos (by positivity : 0 < 1 + |r|) (-(α + 2))).trans_le ?_
  rw [normalizer_eq_circleAverage_radius, ← Real.circleAverage_const ((1 + |r|) ^ (-(α + 2))) 0 r]
  refine Real.circleAverage_mono continuousOn_const.circleIntegrable'
    ((continuousOn_boundaryKernel_norm _ fun _ hz ↦ by
      simpa only [Metric.mem_sphere, dist_zero_right] using lt_of_eq_of_lt hz hr).circleIntegrable')
    fun z hz ↦ ?_
  have hz' : ‖z‖ = |r| := by simpa using hz
  have hn : 0 < ‖1 - z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) z
    simp only [norm_one, hz'] at h
    exact (sub_pos.mpr hr).trans_le h
  exact Real.rpow_le_rpow_of_nonpos hn
    (by simpa only [norm_one, hz'] using norm_sub_le (1 : ℂ) z) (by linarith)

/-- Duplication expresses the proposed sharp constant in the boundary beta-integral form. -/
theorem gammaConstant_eq_boundaryGamma {α : ℝ} (hα : -1 < α) :
    gammaConstant α =
      2 ^ α * Real.Gamma ((α + 1) / 2) /
        (Real.sqrt Real.pi * Real.Gamma (1 + α / 2)) := by
  have hG := Real.Gamma_mul_Gamma_add_half_of_pos (show 0 < (α + 1) / 2 by linarith)
  rw [show (α + 1) / 2 + 1 / 2 = 1 + α / 2 by ring,
    show 2 * ((α + 1) / 2) = α + 1 by ring,
    show 1 - (α + 1) = -α by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hG
  have htwo : (2 : ℝ) ^ α ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) α).ne'
  have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hGamma : Real.Gamma ((2 + α) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  unfold gammaConstant
  field_simp at hG ⊢
  linear_combination -hG

theorem circleAverage_boundary_power {α : ℝ} (hα : -1 < α) :
    Real.circleAverage (fun ζ : ℂ ↦ ‖1 - ζ‖ ^ α) 0 1 = gammaConstant α := by
  rw [Real.circleAverage_def]
  have heq : (∫ θ in (0 : ℝ)..2 * Real.pi, ‖1 - circleMap 0 1 θ‖ ^ α) =
      2 ^ α * (∫ θ in (0 : ℝ)..2 * Real.pi, Real.sin (θ / 2) ^ α) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_Ioo_of_le (by positivity) fun θ hθ ↦ ?_
    have hs : 0 ≤ Real.sin (θ / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    rw [circleMap, zero_add, Complex.ofReal_one, one_mul, norm_sub_rev,
      mul_comm (θ : ℂ) Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hs), Real.mul_rpow (by norm_num) hs]
  rw [heq, intervalIntegral.integral_comp_div (fun θ ↦ Real.sin θ ^ α) (by norm_num)]
  simp only [zero_div, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), smul_eq_mul]
  rw [integral_sin_rpow hα, gammaConstant_eq_boundaryGamma hα]
  have hpi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hpi0 : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hG : Real.Gamma (1 + α / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  field_simp; rw [hpi]

theorem norm_boundaryKernel_circleMap_sq (r θ : ℝ) :
    ‖1 - (r : ℂ) * circleMap 0 1 θ‖ ^ 2 = circleDenominator r (Real.cos θ) := by
  have hn : Complex.normSq (Complex.exp ((θ : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.sq_norm]; simp
  simp [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_mul, hn, circleDenominator, circleMap]
  ring

theorem norm_boundaryKernel_circleMap_rpow (p r θ : ℝ) :
    ‖1 - (r : ℂ) * circleMap 0 1 θ‖ ^ p =
      circleDenominator r (Real.cos θ) ^ (p / 2) := by
  rw [← norm_boundaryKernel_circleMap_sq, ← Real.rpow_natCast _ 2,
    ← Real.rpow_mul (norm_nonneg _)]
  congr 1; ring

theorem circleAverage_radialKernel_eq_arcsine (p : ℝ) {r : ℝ} (hr : |r| < 1) :
    Real.circleAverage (fun ζ : ℂ ↦ ‖1 - (r : ℂ) * ζ‖ ^ p) 0 1 =
      Real.pi⁻¹ * (∫ x in (-1 : ℝ)..1,
        circleDenominator r x ^ (p / 2) / Real.sqrt (1 - x ^ 2)) := by
  let F : ℝ → ℝ := fun x ↦ circleDenominator r x ^ (p / 2)
  have hc : Continuous fun θ ↦ F (Real.cos θ) :=
    Continuous.rpow_const (by unfold circleDenominator; fun_prop) fun θ ↦
      Or.inl (circleDenominator_pos hr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩).ne'
  have heq : (∫ θ in Real.pi..2 * Real.pi, F (Real.cos θ)) =
      ∫ θ in (0 : ℝ)..Real.pi, F (Real.cos θ) := by
    conv_lhs => arg 1; intro θ; rw [← Real.cos_two_pi_sub θ]
    rw [intervalIntegral.integral_comp_sub_left (fun θ ↦ F (Real.cos θ)), sub_self,
      show 2 * Real.pi - Real.pi = Real.pi by ring]
  have harc : (∫ θ in (0 : ℝ)..Real.pi, F (Real.cos θ)) =
      ∫ x in (-1 : ℝ)..1, F x / Real.sqrt (1 - x ^ 2) := by
    have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
      (a := (0 : ℝ)) (b := Real.pi) (f := Real.cos) (f' := fun θ ↦ -Real.sin θ)
      (g := fun x ↦ F x / Real.sqrt (1 - x ^ 2)) Real.continuous_cos.continuousOn
      (fun θ _ ↦ Real.hasDerivAt_cos θ)
      (fun θ hθ ↦ by
        rw [min_eq_left Real.pi_pos.le, max_eq_right Real.pi_pos.le] at hθ
        exact neg_nonpos.mpr (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2.le))
    rw [Real.cos_zero, Real.cos_pi,
      intervalIntegral.integral_symm (f := fun x ↦ F x / Real.sqrt (1 - x ^ 2))] at hsub
    apply neg_injective
    rw [← hsub, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le fun θ hθ ↦ ?_
    dsimp only [Function.comp_def]
    have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    rw [show 1 - Real.cos θ ^ 2 = Real.sin θ ^ 2 by nlinarith [Real.sin_sq_add_cos_sq θ],
      Real.sqrt_sq_eq_abs, abs_of_pos hs]
    field_simp
  rw [Real.circleAverage_def]
  simp_rw [norm_boundaryKernel_circleMap_rpow]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := Real.pi) (c := 2 * Real.pi)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), heq, harc]
  simp only [smul_eq_mul, F]; ring

/-- The exact Möbius identity for the weighted boundary-kernel normalizer. -/
theorem radialMass_mul_normalizer (α : ℝ) {r : ℝ} (hr : |r| < 1) :
    (1 - r ^ 2) ^ (α + 1) * normalizer α r =
      Real.circleAverage (fun ζ : ℂ ↦ ‖1 - (r : ℂ) * ζ‖ ^ α) 0 1 := by
  unfold normalizer
  rw [circleAverage_radialKernel_eq_arcsine _ hr, circleAverage_radialKernel_eq_arcsine _ hr,
    ← mul_left_comm]
  congr 1
  let F (x : ℝ) := circleDenominator r x ^ (-(α + 2) / 2)
  let m (x : ℝ) := (2 * r - (1 + r ^ 2) * x) / circleDenominator r x
  have hδ : 0 < 1 - r ^ 2 := by
    rcases abs_lt.mp hr with ⟨hr₁, hr₂⟩
    nlinarith [mul_pos (by linarith : 0 < 1 + r) (by linarith : 0 < 1 - r)]
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := (-1 : ℝ)) (b := 1) (f := m)
    (f' := fun x ↦ -(1 - r ^ 2) ^ 2 / circleDenominator r x ^ 2)
    (g := fun x ↦ F x / Real.sqrt (1 - x ^ 2))
    (by
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact ContinuousOn.div (by fun_prop) (by unfold circleDenominator; fun_prop)
        fun x hx ↦ (circleDenominator_pos hr hx).ne')
    (fun x hx ↦ by
      norm_num at hx
      have hd0 := (circleDenominator_pos hr ⟨hx.1.le, hx.2.le⟩).ne'
      convert! (((hasDerivAt_id x).const_mul (1 + r ^ 2)).const_sub (2 * r)).div
        (((hasDerivAt_id x).const_mul (2 * r)).const_sub (1 + r ^ 2)) hd0 using 1
      unfold circleDenominator; simp only [id_eq]; ring)
    (fun x _ ↦ div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (sq_nonneg _))
  have hm1 : m (-1) = 1 :=
    (div_eq_iff (circleDenominator_pos hr ⟨le_rfl, by norm_num⟩).ne').mpr
      (by unfold circleDenominator; ring)
  have h1 : m 1 = -1 :=
    (div_eq_iff (circleDenominator_pos hr ⟨by norm_num, le_rfl⟩).ne').mpr
      (by unfold circleDenominator; ring)
  rw [hm1, h1, intervalIntegral.integral_symm (f := fun x ↦ F x / Real.sqrt (1 - x ^ 2))] at hsub
  rw [show (∫ x in (-1 : ℝ)..1, circleDenominator r x ^ (-(α + 2) / 2) / Real.sqrt (1 - x ^ 2)) =
    ∫ x in (-1 : ℝ)..1, F x / Real.sqrt (1 - x ^ 2) from rfl]
  apply neg_injective
  rw [← mul_neg, ← hsub, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun x hx ↦ ?_
  dsimp only [Function.comp_def, F]
  have hD := circleDenominator_pos hr ⟨hx.1.le, hx.2.le⟩
  have hx₂ : 0 < 1 - x ^ 2 := by
    nlinarith [mul_pos (by linarith [hx.1] : 0 < 1 + x) (sub_pos.mpr hx.2)]
  have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr hx₂
  have hsq : 1 - m x ^ 2 = (1 - r ^ 2) ^ 2 * (1 - x ^ 2) / circleDenominator r x ^ 2 := by
    have := hD.ne'; dsimp [m]; field_simp; unfold circleDenominator; ring
  have hsqrt : Real.sqrt (1 - m x ^ 2) =
      (1 - r ^ 2) * Real.sqrt (1 - x ^ 2) / circleDenominator r x := by
    rw [hsq, Real.sqrt_div (by positivity), Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_pos hδ, abs_of_pos hD]
  have hd_mob : circleDenominator r (m x) = (1 - r ^ 2) ^ 2 / circleDenominator r x := by
    have hd := hD.ne'
    change 1 + r ^ 2 - 2 * r * ((2 * r - (1 + r ^ 2) * x) / circleDenominator r x) = _
    rw [eq_div_iff hd, sub_mul, mul_assoc (2 * r), div_mul_cancel₀ _ hd]
    unfold circleDenominator; ring
  have hδexp : (1 - r ^ 2) ^ (α + 1) * (1 - r ^ 2) = (1 - r ^ 2) ^ (α + 2) := by
    rw [← Real.rpow_add_one hδ.ne', add_assoc, one_add_one_eq_two]
  have hDexp : circleDenominator r x ^ ((α + 2) / 2) =
      circleDenominator r x ^ (α / 2) * circleDenominator r x := by
    rw [show (α + 2) / 2 = α / 2 + 1 by ring, Real.rpow_add hD, Real.rpow_one]
  have hpow : ((1 - r ^ 2) ^ 2 / circleDenominator r x) ^ (-(α + 2) / 2) =
      ((1 - r ^ 2) ^ (α + 2))⁻¹ * circleDenominator r x ^ ((α + 2) / 2) := by
    rw [Real.div_rpow (sq_nonneg _) hD.le, ← Real.rpow_natCast (1 - r ^ 2) 2, ← Real.rpow_mul hδ.le]
    norm_num only [Nat.cast_ofNat]
    rw [show 2 * (-(α + 2) / 2) = -(α + 2) by ring,
      show -(α + 2) / 2 = -((α + 2) / 2) by ring,
      Real.rpow_neg hδ.le, Real.rpow_neg hD.le, div_inv_eq_mul]
  rw [hsqrt, hd_mob, hpow, hDexp]
  have := hD.ne'; have := hδ.ne'; have := hs.ne'
  calc
    _ = -(((1 - r ^ 2) ^ (α + 1) * (1 - r ^ 2)) * ((1 - r ^ 2) ^ (α + 2))⁻¹ *
        circleDenominator r x ^ (α / 2) *
        (circleDenominator r x ^ 2 * (1 - r ^ 2) /
          (circleDenominator r x * (1 - r ^ 2) * circleDenominator r x)) /
        Real.sqrt (1 - x ^ 2)) := by field_simp
    _ = _ := by
      rw [hδexp, mul_inv_cancel₀ (Real.rpow_pos_of_pos hδ _).ne', one_mul]
      field_simp

theorem circleAverage_weightedKernel_norm (α : ℝ) (z : ℂ) {r : ℝ} (_ : 0 ≤ r) :
    Real.circleAverage (fun w ↦ ‖weightedKernel α z w‖) 0 r = normalizer α (r * ‖z‖) := by
  rw [Real.circleAverage_def, normalizer, Real.circleAverage_eq_integral_add (Complex.arg (star z))]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ ↦ ?_
  rw [norm_weightedKernel]
  congr 1
  rw [← norm_star (1 - _), ← norm_star z]
  congr 1
  simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.ofReal_add,
    Complex.ofReal_mul, add_mul, Complex.exp_add, map_sub, map_one, map_mul,
    Complex.conj_ofReal, Complex.star_def, Complex.conj_conj]
  nth_rw 1 [← Complex.norm_mul_exp_arg_mul_I ((starRingEnd ℂ) z)]
  ring

namespace Weighted

abbrev bPI (H : ℝ → ℝ → ℝ → ℝ → ℝ) :=
  polarIntegral H cos sin (volume.restrict (Set.Icc 0 (2 * π))) (fun _ ↦ (2 * π)⁻¹)

private theorem bInt :
    Integrable (fun _ : ℝ ↦ (2 * π)⁻¹) (volume.restrict (Set.Icc 0 (2 * π))) :=
  integrable_const _

private theorem bSrc (t : ℝ) (_ : t ∈ Set.Icc 0 (2 * π)) : cos t ^ 2 + sin t ^ 2 ≤ 1 :=
  (cos_sq_add_sin_sq t).le

local notation "bApp " f:arg =>
  f isCompact_Icc (ae_restrict_mem measurableSet_Icc) bInt continuous_cos continuous_sin bSrc

theorem polarIntegral_boundary_eq_normalizer (α r θ : ℝ) :
    bPI (polarKernel (-(α + 2) / 2)) r θ = normalizer α r := by
  have hk (t : ℝ) : polarKernel (-(α + 2) / 2) (cos t) (sin t) r θ =
      ‖weightedKernel α (circleMap 0 r θ) (circleMap 0 1 t)‖ := by
    simpa only [circleMap_zero_re, circleMap_zero_im, one_mul] using
      polarKernel_eq_norm_weightedKernel α r θ (circleMap 0 1 t)
  have hcircle := circleAverage_weightedKernel_norm α (circleMap 0 r θ) (r := 1) (by norm_num)
  simp only [one_mul, norm_circleMap_zero, normalizer_eq_circleAverage_radius,
    circleAverage_abs_radius] at hcircle ⊢
  rw [bPI, polarIntegral]
  simp_rw [hk]
  rw [integral_mul_const, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  simpa only [Real.circleAverage_def, smul_eq_mul, mul_comm] using hcircle

def normalizerFirst (α r : ℝ) : ℝ := bPI (polarKernelR (-(α + 2) / 2)) r 0

def normalizerSecond (α r : ℝ) : ℝ := bPI (polarKernelRR (-(α + 2) / 2)) r 0

theorem normalizer_hasDerivAt (α : ℝ) {r : ℝ} (hr : r ^ 2 < 1) :
    HasDerivAt (normalizer α) (normalizerFirst α r) r := by
  simpa only [polarIntegral_boundary_eq_normalizer, normalizerFirst] using
    (bApp polarIntegral_kernel_hasDerivAt_r) (-(α + 2) / 2) hr 0

theorem normalizerFirst_hasDerivAt (α : ℝ) {r : ℝ} (hr : r ^ 2 < 1) :
    HasDerivAt (normalizerFirst α) (normalizerSecond α r) r :=
  (bApp polarIntegral_kernelR_hasDerivAt_r) (-(α + 2) / 2) hr 0

private theorem bCont {H : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hH : polarKernelCont (Set.Icc 0 (2 * π)) cos sin H) :
    ContinuousOn (fun r ↦ bPI H r 0) (Set.Ico 0 1) := by
  apply (continuousOn_polarIntegral_unit isCompact_Icc (ae_restrict_mem measurableSet_Icc)
    bInt hH).comp (continuous_id.prodMk continuous_const).continuousOn
  exact fun _ hr ↦ ⟨hr, Set.mem_univ _⟩

theorem continuousOn_normalizerFirst (α : ℝ) :
    ContinuousOn (normalizerFirst α) (Set.Ico 0 1) :=
  bCont (continuousOn_polarKernelR_source continuous_cos continuous_sin bSrc _)

theorem continuousOn_normalizerSecond (α : ℝ) :
    ContinuousOn (normalizerSecond α) (Set.Ico 0 1) :=
  bCont (continuousOn_polarKernelRR_source continuous_cos continuous_sin bSrc _)

/-- The exact radial differential equation for the normalizing circular average. -/
theorem normalizer_ode (α : ℝ) {r : ℝ} (hr : r ^ 2 < 1) (hr0 : r ≠ 0) :
    normalizerSecond α r + normalizerFirst α r / r -
      (2 * (α + 2) * r / (1 - r ^ 2)) * normalizerFirst α r -
      ((α + 2) ^ 2 / (1 - r ^ 2)) * normalizer α r = 0 := by
  have hd1 (θ : ℝ) : bPI (polarKernelT (-(α + 2) / 2)) r θ = 0 := by
    have hd : HasDerivAt (bPI (polarKernel (-(α + 2) / 2)) r) _ θ :=
      (bApp polarIntegral_kernel_hasDerivAt_t) (-(α + 2) / 2) hr θ
    rw [funext (polarIntegral_boundary_eq_normalizer α r)] at hd
    exact hd.unique (hasDerivAt_const θ _)
  have hd2 : bPI (polarKernelTT (-(α + 2) / 2)) r 0 = 0 := by
    have hd : HasDerivAt (bPI (polarKernelT (-(α + 2) / 2)) r) _ 0 :=
      (bApp polarIntegral_kernelT_hasDerivAt_t) (-(α + 2) / 2) hr 0
    rw [funext hd1] at hd
    exact hd.unique (hasDerivAt_const 0 0)
  have heq := (bApp polarIntegral_operator) (α + 2) hr hr0 0
  unfold polarOperator at heq
  simp only [cos_sq_add_sin_sq, sub_self, mul_zero, neg_zero, zero_div, zero_mul,
    integral_zero] at heq
  rw [normalizerFirst, normalizerSecond, ← polarIntegral_boundary_eq_normalizer α r 0]
  linear_combination heq - hd2 / r ^ 2

end Weighted

open Weighted

theorem normalizer_mono (α : ℝ) {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r ≤ R) (hR : R < 1) : normalizer α r ≤ normalizer α R := by
  have hr2 {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) : x ^ 2 < 1 := by nlinarith
  have hw : ContinuousOn (fun x : ℝ ↦ (1 - x ^ 2) ^ (α + 2)) (Set.Ico 0 1) :=
    (continuousOn_const.sub (continuousOn_id.pow 2)).rpow_const fun x hx ↦
      Or.inl (sub_pos.mpr (hr2 hx.1 hx.2)).ne'
  refine neg_le_neg_iff.mp (antitoneOn_of_radial_flux (M' := fun x ↦ -normalizerFirst α x)
    (w := fun x ↦ (1 - x ^ 2) ^ (α + 2))
    (F := fun x ↦ x * (1 - x ^ 2) ^ (α + 2) * -normalizerFirst α x)
    (F' := fun x ↦ -((1 - x ^ 2) ^ (α + 2) * (x * normalizerSecond α x +
      normalizerFirst α x - 2 * (α + 2) * x ^ 2 / (1 - x ^ 2) * normalizerFirst α x)))
    (continuousOn_normalizer α).neg
    (fun x hx ↦ (normalizer_hasDerivAt α (hr2 hx.1.le hx.2)).neg)
    (fun x hx ↦ Real.rpow_pos_of_pos (sub_pos.mpr (hr2 hx.1.le hx.2)) _)
    ((continuousOn_id.mul hw).mul (continuousOn_normalizerFirst α).neg) (by simp)
    (fun x hx ↦ ?_) (fun x hx ↦ ?_) (fun _ _ ↦ rfl)
    ⟨hr, hrR.trans_lt hR⟩ ⟨hr.trans hrR, hR⟩ hrR)
  · have ht : 0 < 1 - x ^ 2 := sub_pos.mpr (hr2 hx.1.le hx.2)
    have hwd := (((hasDerivAt_id x).pow 2).const_sub 1).rpow_const (p := α + 2) (Or.inl ht.ne')
    convert ((hasDerivAt_id x).mul hwd).mul
      (normalizerFirst_hasDerivAt α (hr2 hx.1.le hx.2)).neg using 1
    · rfl
    · dsimp only [Pi.pow_apply, Pi.mul_apply, Pi.neg_apply, id_eq]
      rw [Real.rpow_sub_one ht.ne']
      field_simp [ht.ne']
      ring
  · have ht : 0 < 1 - x ^ 2 := sub_pos.mpr (hr2 hx.1.le hx.2)
    have hode := normalizer_ode α (hr2 hx.1.le hx.2) hx.1.ne'
    have heq : x * normalizerSecond α x + normalizerFirst α x -
        2 * (α + 2) * x ^ 2 / (1 - x ^ 2) * normalizerFirst α x =
        x * (normalizerSecond α x + normalizerFirst α x / x -
          (2 * (α + 2) * x / (1 - x ^ 2)) * normalizerFirst α x -
          ((α + 2) ^ 2 / (1 - x ^ 2)) * normalizer α x) +
        x * ((α + 2) ^ 2 / (1 - x ^ 2)) * normalizer α x := by
      field_simp [hx.1.ne', ht.ne']
      ring
    rw [heq, hode, mul_zero, zero_add]
    exact neg_nonpos.mpr (mul_nonneg (Real.rpow_nonneg ht.le _)
      (mul_nonneg (mul_nonneg hx.1.le (div_nonneg (sq_nonneg _) ht.le))
        (normalizer_nonneg α x)))

end BergmanWeakType
