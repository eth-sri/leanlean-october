/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import BergmanWeakType.PolarMeasure
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Distribution estimates from increasing truncations in a radial mass coordinate -/

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Set
open scoped Topology

namespace BergmanWeakType.Weighted

/-- Integrate a one-sided difference bound using the integral estimate for slopes
of a monotone function. Neither a derivative nor measurability of `A` is required. -/
theorem integral_le_of_slope_bound {α : ℝ} {A G : ℝ → ℝ} (hm : MonotoneOn G (Icc 0 1))
    (hs : ∀ x y : ℝ, 0 < x → x < y → y < 1 → (exteriorMass α x-exteriorMass α y)*A x ≤ G y-G x) :
    (∫ x in (0:ℝ)..1, radialDensity α x * A x) ≤ G 1 - G 0 := by
  have nonneg := sub_nonneg.mpr (hm (by simp) (by simp) zero_le_one)
  by_cases hi : IntervalIntegrable (fun x ↦ radialDensity α x * A x) volume 0 1
  · have m : MonotoneOn G (uIcc 0 1) := by simpa
    have H := m.intervalIntegral_deriv_mem_uIcc
    rw [uIcc_of_le nonneg] at H
    apply le_trans (intervalIntegral.integral_mono_ae_restrict zero_le_one hi m.intervalIntegrable_deriv ?_) H.2
    rw [← restrict_Ioo_eq_restrict_Icc, Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hm.ae_differentiableWithinAt_of_mem] with x hd hx
    have D := ((hd (Ioo_subset_Icc_self hx)).differentiableAt (by simp_all)).hasDerivAt
    have W := hasDerivAt_iff_tendsto_slope_left_right.mp (exteriorMass_deriv (α := α) (inner_sq hx))
    apply le_of_tendsto_of_tendsto (by simpa using W.2.neg.mul_const (A x)) (hasDerivAt_iff_tendsto_slope_left_right.mp D).2
    filter_upwards [Ioo_mem_nhdsGT hx.2] with y hy
    simp only [slope_def_field, ← neg_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (sub_pos.mpr hy.1)]
    grind [exteriorMass]
  · rwa [intervalIntegral.integral_undef hi]

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def capMean (U : ℝ → X → ℝ) (y c : ℝ) := ∫ z, min (U y z) c ∂μ

/-- Moving the cap from `t*x` to `t*y` pays at least `t*(y-x)` on the section
of `E` at `y`. Monotonicity of fixed-cap means lets us sum these increments. -/
theorem moving_cap_bound {α : ℝ} (hα : -1 < α) {U : ℝ → X → ℝ} (meas : ∀ y, Measurable (U y))
    (pos : ∀ y z, 0 ≤ U y z) {t : ℝ} (ht : 0 ≤ t) {E : Set (ℝ × X)} (me : MeasurableSet E)
    (sub : ∀ y ∈ radii, ∀ z, (y,z) ∈ E → t*exteriorMass α y ≤ U y z)
    (mono : ∀ c, AntitoneOn (fun y ↦ capMean μ U y c) radii) :
    t * ((radialLaw α).prod μ).real E ≤ capMean μ U 0 t := by
  let := radialLaw_prob hα
  let B y := Prod.mk y ⁻¹' E
  let Y := exteriorMass α
  let G y := -capMean μ U y (t*Y y)
  have ep : Y 1 = 0 := by grind [exteriorMass, Real.zero_rpow]
  have capI y {c : ℝ} (hc : 0 ≤ c) : Integrable (fun z ↦ min (U y z) c) μ :=
    (integrable_const c).mono' (by fun_prop)
      (by simp_all [abs_of_nonneg])
  have inc {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ 1) :
      (Y x-Y y) * (t * μ.real (B x)) ≤ G y-G x := by
    have hx' : x ∈ radii := ⟨hx,hxy.trans_le hy⟩
    have hy' : y ∈ Icc 0 1 := ⟨hx.trans hxy.le,hy⟩
    have hy0 := (mass_anti hα).antitoneOn hy' (by simp) hy
    have m := (mass_anti hα).antitoneOn (Ico_subset_Icc_self hx') hy' hxy.le
    have mt : t*Y y ≤ t*Y x := mul_le_mul_of_nonneg_left m ht
    have h : capMean μ U y (t*Y y) ≤ capMean μ U x (t*Y y) := by
      rcases hy.eq_or_lt with rfl|hlt
      · grind [capMean]
      · exact mono _ hx' ⟨hy'.1,hlt⟩ hxy.le
    have meB : MeasurableSet (B x) := measurable_prodMk_left me
    have dif : (t*Y x-t*Y y) * μ.real (B x) ≤ capMean μ U x (t*Y x) - capMean μ U x (t*Y y) := by
      change Y 1 ≤ Y y at hy0; rw [ep] at hy0
      rw [← integral_indicator_one meB, ← integral_const_mul,capMean,capMean,
        ← integral_sub (capI _ (by bound)) (capI _ (by bound))]
      apply integral_mono (((integrable_const 1).indicator meB).const_mul _) (by fun_prop (disch := bound))
      intro z; by_cases hz : z ∈ B x
      · have hu : t*Y x ≤ U x z := sub x hx' z hz
        simp_all [mt.trans]
      · simp_all
    dsimp [G]; linarith
  rw [measureReal_def,Measure.prod_apply me, ← integral_toReal (measurable_measure_prodMk_left me).aemeasurable
    (by simp_all), ← integral_const_mul,integral_radialLaw hα,← unit_integral]
  apply le_trans (integral_le_of_slope_bound (G := G) (A := fun x ↦ t*μ.real (B x)) ?_ (by grind [exteriorMass]))
  · simp [G,ep,capMean,min_eq_right (pos _ _),Y,exteriorMass,Real.zero_rpow (by linarith : α+1 ≠ 0)]
  · intro x hx y hy hxy
    rcases hxy.eq_or_lt with rfl|hlt; · rfl
    exact sub_nonneg.mp ((mul_nonneg (sub_nonneg.mpr ((mass_anti hα).antitoneOn hx hy hxy)) (by positivity)).trans (inc hx.1 hlt hy.2))

end BergmanWeakType.Weighted
