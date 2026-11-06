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

public section

open MeasureTheory Set Filter Topology

namespace DOZZ.Proofs

theorem integrable_mul_brownianHeatDensity {t : ℝ} (ht : 0 < t) :
    Integrable (fun z : ℝ => z * brownianHeatDensity t z) (volume : Measure ℝ) := by
  have hcoef : 0 < 1 / (2 * t) := by positivity

  have hbase := integrable_mul_exp_neg_mul_sq hcoef
  have hmul := hbase.mul_const ((Real.sqrt (2 * Real.pi * t))⁻¹)
  refine hmul.congr ?_
  filter_upwards [] with z
  have hq : brownianHeatDensity t z =
      Real.exp (-(1 / (2 * t)) * z ^ 2) * (Real.sqrt (2 * Real.pi * t))⁻¹ := by
    simp only [brownianHeatDensity, ite_eq_left ht]
    ring
  rw [hq]
  ring

variable {t a : ℝ} (ht : 0 < t)

include t a ht in
private theorem integrable_mul_brownianHeatDensity_translate  :
    Integrable (fun y : ℝ => (y + a) * brownianHeatDensity t (y + a))
      (volume : Measure ℝ) := by
  have he  :=
    (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding
  have hmap : (volume : Measure ℝ).map (fun y : ℝ => y + a) = volume :=
    Measure.IsAddRightInvariant.map_add_right_eq_self a
  have hmapInt : Integrable (fun z : ℝ => z * brownianHeatDensity t z)
      ((volume : Measure ℝ).map (fun y : ℝ => y + a)) := by
    rw [hmap]
    exact integrable_mul_brownianHeatDensity ht
  exact he.integrable_map_iff.mp hmapInt

private theorem brownianHeatDensity_hasDerivAt {t z : ℝ} (ht : 0 < t) :
    HasDerivAt (brownianHeatDensity t) (-(z / t) * brownianHeatDensity t z) z := by

  have harg : HasDerivAt (fun w : ℝ => -(w ^ 2) / (2 * t)) (-(z / t)) z := by
    convert ((hasDerivAt_id z).pow 2).const_mul (-(1 / (2 * t))) using 1
    · funext w
      field_simp [ht.ne']
      rfl
    grind
  have hexp := (Real.hasDerivAt_exp _).comp z harg
  have hqfun : brownianHeatDensity t = fun w : ℝ =>
      Real.exp (-(w ^ 2) / (2 * t)) * (Real.sqrt (2 * Real.pi * t))⁻¹ := by
    funext w
    simp only [brownianHeatDensity, ite_eq_left ht, div_eq_mul_inv]
  rw [hqfun]
  convert hexp.const_mul ((Real.sqrt (2 * Real.pi * t))⁻¹) using 1
  all_goals grind

include t a ht in
private theorem integrableOn_mul_brownianHeatDensity_translate  :
    IntegrableOn (fun y : ℝ => (y + a) * brownianHeatDensity t (y + a))
      (Set.Ioi 0) (volume : Measure ℝ) :=
  (integrable_mul_brownianHeatDensity_translate ht).integrableOn

include t a ht in
/-- A Gaussian first-moment tail is its heat-kernel boundary value. -/
private theorem integral_brownianHeatDensity_linear_tail  :
    ∫ y in Set.Ioi 0, (y + a) * brownianHeatDensity t (y + a)
      ∂(volume : Measure ℝ) = t * brownianHeatDensity t a := by
  let F  := fun y => -t * brownianHeatDensity t (y + a)
  have hderiv : ∀ y ∈ Set.Ici 0,
      HasDerivAt F ((y + a) * brownianHeatDensity t (y + a)) y := by
    intro y hy
    have hshift  := (hasDerivAt_id y).add_const a
    have hq := (brownianHeatDensity_hasDerivAt (t := t) (z := y + a) ht).comp y hshift
    have hF := hq.const_mul (-t)
    grind
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
    grind
  have hqtendsto : Tendsto (fun y : ℝ => brownianHeatDensity t (y + a)) atTop (𝓝 0) := by
    have hexp := Real.tendsto_exp_atBot.comp harg

    simpa [brownianHeatDensity, ht, div_eq_mul_inv, mul_comm] using
      hexp.const_mul ((Real.sqrt (2 * Real.pi * t))⁻¹)
  have hF_tendsto : Tendsto F atTop (𝓝 0) := by
    simpa [F] using hqtendsto.const_mul (-t)
  have hint := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrableOn_mul_brownianHeatDensity_translate ht) hF_tendsto
  simpa [F] using hint

include t a ht in
private theorem integrable_brownianHeatDensity_translate_local  :
    Integrable (fun y : ℝ => brownianHeatDensity t (y + a)) (volume : Measure ℝ) := by
  have he  :=
    (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding
  have hmap : (volume : Measure ℝ).map (fun y : ℝ => y + a) = volume :=
    Measure.IsAddRightInvariant.map_add_right_eq_self a
  have hmapInt : Integrable (brownianHeatDensity t)
      ((volume : Measure ℝ).map (fun y : ℝ => y + a)) := by
    rw [hmap]
    exact integrable_brownianHeatDensity ht
  exact he.integrable_map_iff.mp hmapInt

include t a ht in
private theorem integrableOn_brownianHeatDensity_translate  :
    IntegrableOn (fun y : ℝ => brownianHeatDensity t (y + a))
      (Set.Ioi 0) (volume : Measure ℝ) :=
  (integrable_brownianHeatDensity_translate_local ht).integrableOn

/-- The BES(3) Doob transition density has unit mass on the positive half-line. -/
theorem conditionedPositiveTransitionDensity_integral_eq_one_zero
    {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    ∫ y in Set.Ioi 0, conditionedPositiveTransitionDensity 0 t x y
      ∂(volume : Measure ℝ) = 1 := by
  have hfirst :
      (∫ y in Set.Ioi 0, y *
          (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x))
          ∂(volume : Measure ℝ)) = x := by
    have hlin :
        (∫ y in Set.Ioi 0,
          ((y - x) * brownianHeatDensity t (y - x) -
            (y + x) * brownianHeatDensity t (y + x) +
            x * (brownianHeatDensity t (y - x) + brownianHeatDensity t (y + x)))
          ∂(volume : Measure ℝ)) = x := by
      have hleft := integral_brownianHeatDensity_linear_tail (t := t) (a := -x) ht
      have hright := integral_brownianHeatDensity_linear_tail (t := t) (a := x) ht
      have hpair := integral_brownianHeatDensity_halfline_pair (t := t) (a := x) ht
      have hA : IntegrableOn (fun y : ℝ => (y - x) * brownianHeatDensity t (y - x))
          (Set.Ioi 0) (volume : Measure ℝ) := integrableOn_mul_brownianHeatDensity_translate ht
      have hB := integrableOn_mul_brownianHeatDensity_translate (t := t) (a := x) ht
      have hqA : IntegrableOn (fun y : ℝ => brownianHeatDensity t (y - x))
          (Set.Ioi 0) (volume : Measure ℝ) := integrableOn_brownianHeatDensity_translate ht
      have hqB := integrableOn_brownianHeatDensity_translate (t := t) (a := x) ht
      have hsumInt  := hqA.add hqB
      have hsumMul  :=
        hsumInt.integrable.const_mul x
      have hleft' :
          ∫ y in Set.Ioi 0, (y - x) * brownianHeatDensity t (y - x)
            ∂(volume : Measure ℝ) = t * brownianHeatDensity t (-x) := hleft
      calc
        _ = ∫ y in Set.Ioi 0,
              ((y - x) * brownianHeatDensity t (y - x) -
                (y + x) * brownianHeatDensity t (y + x) +
                x * (brownianHeatDensity t (y - x) + brownianHeatDensity t (y + x)))
              ∂(volume : Measure ℝ) := by
            simp_all
        _ = (∫ y in Set.Ioi 0, (y - x) * brownianHeatDensity t (y - x)
                ∂(volume : Measure ℝ)) -
              ∫ y in Set.Ioi 0, (y + x) * brownianHeatDensity t (y + x)
                ∂(volume : Measure ℝ) +
              x * (∫ y in Set.Ioi 0,
                brownianHeatDensity t (y - x) + brownianHeatDensity t (y + x)
                ∂(volume : Measure ℝ)) := by
            calc
              _ = (∫ y in Set.Ioi 0,
                    (y - x) * brownianHeatDensity t (y - x) -
                      (y + x) * brownianHeatDensity t (y + x)
                    ∂(volume : Measure ℝ)) +
                  ∫ y in Set.Ioi 0,
                    x * (brownianHeatDensity t (y - x) + brownianHeatDensity t (y + x))
                    ∂(volume : Measure ℝ) :=
                  integral_add (hA.sub hB) hsumMul
              _ = _ := by
                  rw [integral_sub hA hB, integral_const_mul]
        _ = t * brownianHeatDensity t (-x) - t * brownianHeatDensity t x + x * 1 := by
            rw [hleft', hright, integral_add hqA hqB, hpair]
        _ = x := by
            have heven : brownianHeatDensity t (-x) = brownianHeatDensity t x := by
              simp [brownianHeatDensity, ht]
            rw [heven]
            ring
    grind
  have hkernel : ∀ y : ℝ, 0 < y →
      conditionedPositiveTransitionDensity 0 t x y =
        (y / x) * (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x)) := by
    intro y hy
    simp [conditionedPositiveTransitionDensity, conditionedH, ht, hx, hy]
    ring
  have hscale :
      (∫ y in Set.Ioi 0, (y / x) *
        (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x))
        ∂(volume : Measure ℝ)) = 1 := by
    rw [show (fun y : ℝ => (y / x) *
        (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x))) =
        fun y => x⁻¹ * (y *
          (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x))) by
          funext y
          field_simp [hx.ne']]
    rw [integral_const_mul, hfirst]
    field_simp [hx.ne']
  rw [setIntegral_congr_fun measurableSet_Ioi]
  all_goals continuity

end DOZZ.Proofs

end
