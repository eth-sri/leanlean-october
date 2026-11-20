/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelNormalization
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Normalization of the zero-drift conditioned kernel

The BES(3) transition mass is reduced to two Gaussian first-moment tails. Their primitive
boundary terms cancel by heat-kernel symmetry, and the remaining term is the reflected
half-line Gaussian mass.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace DOZZ.Proofs

theorem integrable_mul_brownianHeatDensity {t : ℝ} (ht : 0 < t) :
    Integrable (fun z : ℝ => z * brownianHeatDensity t z) (volume : Measure ℝ) := by
  have hcoef : 0 < 1 / (2 * t) := by positivity
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * t) := by positivity
  have hbase := integrable_mul_exp_neg_mul_sq hcoef
  have hmul := hbase.mul_const ((Real.sqrt (2 * Real.pi * t))⁻¹)
  refine hmul.congr ?_
  filter_upwards [] with z
  have hq : brownianHeatDensity t z =
      Real.exp (-(1 / (2 * t)) * z ^ 2) * (Real.sqrt (2 * Real.pi * t))⁻¹ := by
    simp only [brownianHeatDensity, ite_eq_left ht]
    rw [div_eq_mul_inv]
    congr 1
    field_simp [ht.ne', hsqrt.ne']
  rw [hq]
  ring

private theorem brownianHeatDensity_hasDerivAt {t z : ℝ} (ht : 0 < t) :
    HasDerivAt (brownianHeatDensity t) (-(z / t) * brownianHeatDensity t z) z := by
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * t) := by positivity
  have harg : HasDerivAt (fun w : ℝ => -(w ^ 2) / (2 * t)) (-(z / t)) z := by
    convert ((hasDerivAt_id z).pow 2).const_mul (-(1 / (2 * t))) using 1
    · funext w
      field_simp [ht.ne']
      rfl
    · field_simp [ht.ne']
      norm_num [id]
      ring
  have hexp := (Real.hasDerivAt_exp _).comp z harg
  have hqfun : brownianHeatDensity t = fun w : ℝ =>
      Real.exp (-(w ^ 2) / (2 * t)) * (Real.sqrt (2 * Real.pi * t))⁻¹ := by
    funext w
    simp only [brownianHeatDensity, ite_eq_left ht, div_eq_mul_inv]
  rw [hqfun]
  convert hexp.const_mul ((Real.sqrt (2 * Real.pi * t))⁻¹) using 1
  · funext w
    simp only [Function.comp_apply]
    ring
  · field_simp [ht.ne', hsqrt.ne']

section
variable {t a : ℝ} (ht : 0 < t)
include ht

private theorem integrableOn_mul_brownianHeatDensity_translate :
    IntegrableOn (fun y : ℝ => (y + a) * brownianHeatDensity t (y + a))
      (Set.Ioi 0) (volume : Measure ℝ) :=
  ((integrable_mul_brownianHeatDensity ht).comp_add_right a).integrableOn

/-- A Gaussian first-moment tail is its heat-kernel boundary value. -/
private theorem integral_brownianHeatDensity_linear_tail :
    ∫ y in Set.Ioi 0, (y + a) * brownianHeatDensity t (y + a)
      ∂(volume : Measure ℝ) = t * brownianHeatDensity t a := by
  let F  := fun y => -t * brownianHeatDensity t (y + a)
  have hderiv : ∀ y ∈ Set.Ici 0,
      HasDerivAt F ((y + a) * brownianHeatDensity t (y + a)) y := by
    intro y hy
    have hshift  := (hasDerivAt_id y).add_const a
    have hq := (brownianHeatDensity_hasDerivAt (t := t) (z := y + a) ht).comp y hshift
    have hF := hq.const_mul (-t)
    convert hF using 1
    rfl
    · field_simp [ht.ne']
  have harg : Tendsto (fun y : ℝ => -((y + a) ^ 2) / (2 * t)) atTop atBot := by
    have hpow : Tendsto (fun y : ℝ => (y + a) ^ 2) atTop atTop := by
      refine Filter.tendsto_atTop.2 ?_
      intro b
      refine Filter.eventually_atTop.2 ⟨max 1 b - a, ?_⟩
      intro y hy
      have h1 : 1 ≤ y + a := by have := le_max_left (1 : ℝ) b; linarith
      have hb : b ≤ y + a := by have := le_max_right (1 : ℝ) b; linarith
      have hz : 0 ≤ y + a := le_trans (by norm_num) h1
      have hprod : 0 ≤ (y + a) * (y + a - 1) := mul_nonneg hz (by linarith)
      nlinarith
    have hcoef : 0 < 1 / (2 * t) := by positivity
    have hscale := hpow.const_mul_atTop_of_neg (neg_lt_zero.mpr hcoef)
    convert hscale using 1
    field_simp [ht.ne']
  have hqtendsto : Tendsto (fun y : ℝ => brownianHeatDensity t (y + a)) atTop (𝓝 0) := by
    have hexp := Real.tendsto_exp_atBot.comp harg
    simpa [brownianHeatDensity, ht, div_eq_mul_inv, mul_comm] using
      hexp.const_mul ((Real.sqrt (2 * Real.pi * t))⁻¹)
  have hF_tendsto : Tendsto F atTop (𝓝 0) := by
    simpa [F] using hqtendsto.const_mul (-t)
  have hint := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrableOn_mul_brownianHeatDensity_translate ht) hF_tendsto
  simpa [F] using hint

end

/-- The BES(3) Doob transition density has unit mass on the positive half-line. -/
theorem conditionedPositiveTransitionDensity_integral_eq_one_zero
    {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    ∫ y in Set.Ioi 0, conditionedPositiveTransitionDensity 0 t x y = 1 := by
  have hker (y : ℝ) (hy : y ∈ Set.Ioi 0) :
      conditionedPositiveTransitionDensity 0 t x y =
        ((y + -x) * brownianHeatDensity t (y + -x) -
          (y + x) * brownianHeatDensity t (y + x) + x * brownianHeatPair t x y) / x := by
    have hk : (0 : ℝ) ≤ 0 ∧ 0 < t ∧ 0 < x ∧ 0 < y := ⟨le_rfl, ht, hx, hy⟩
    simp [conditionedPositiveTransitionDensity, hk, conditionedH, brownianHeatPair, sub_eq_add_neg]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hker, integral_div]
  let F (a y : ℝ) := (y + a) * brownianHeatDensity t (y + a)
  let G (y : ℝ) := x * brownianHeatPair t x y
  change (∫ y in Set.Ioi 0, ((F (-x) - F x) y + G y)) / x = 1
  have hF (a : ℝ) : IntegrableOn (F a) (Set.Ioi 0) :=
    integrableOn_mul_brownianHeatDensity_translate ht
  have hG : IntegrableOn G (Set.Ioi 0) :=
    ((integrable_brownianHeatPair ht x).const_mul x).integrableOn
  rw [integral_add ((hF (-x)).sub (hF x)) hG]
  simp only [Pi.sub_apply]
  rw [integral_sub (hF (-x)) (hF x)]
  dsimp only [F, G]
  rw [integral_brownianHeatDensity_linear_tail ht, integral_brownianHeatDensity_linear_tail ht,
    brownianHeatDensity_even, sub_self, zero_add, integral_const_mul,
    integral_brownianHeatPair ht, mul_one, div_self hx.ne']

end DOZZ.Proofs

end
