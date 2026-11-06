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
  refine ((integrable_mul_exp_neg_mul_sq hcoef).mul_const ((Real.sqrt (2 * Real.pi * t))⁻¹)).congr ?_
  filter_upwards [] with z
  have hq : brownianHeatDensity t z =
      Real.exp (-(1 / (2 * t)) * z ^ 2) * (Real.sqrt (2 * Real.pi * t))⁻¹ := by
    simp only [brownianHeatDensity, ite_eq_left ht]
    ring
  grind

theorem integrable_mul_brownianHeatDensity_translate {t a : ℝ} (ht : 0 < t) :
    Integrable (fun y : ℝ => (y + a) * brownianHeatDensity t (y + a))
      (volume : Measure ℝ) := by
  have he :=
    (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding
  have hmap : (volume : Measure ℝ).map (fun y => y + a) = volume :=
    Measure.IsAddRightInvariant.map_add_right_eq_self a
  have hmapInt : Integrable (fun z => z * brownianHeatDensity t z)
      (volume.map (fun y => y + a)) := by
    rw [hmap]
    exact integrable_mul_brownianHeatDensity ht
  exact he.integrable_map_iff.mp hmapInt

private theorem brownianHeatDensity_hasDerivAt {t z : ℝ} (ht : 0 < t) :
    HasDerivAt (brownianHeatDensity t) (-(z / t) * brownianHeatDensity t z) z := by
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * t) := by positivity
  have harg : HasDerivAt (fun w : ℝ => -(w ^ 2) / (2 * t)) (-(z / t)) z := by
    convert ((hasDerivAt_id z).pow 2).const_mul (-(1 / (2 * t))) using 1
    · funext w
      field_simp [ht.ne']
      rfl
    grind
  have hqfun : brownianHeatDensity t = fun w : ℝ =>
      Real.exp (-(w ^ 2) / (2 * t)) * (Real.sqrt (2 * Real.pi * t))⁻¹ := by
    funext w
    simp only [brownianHeatDensity, ite_eq_left ht, div_eq_mul_inv]
  rw [hqfun]
  convert ((Real.hasDerivAt_exp _).comp z harg).const_mul ((Real.sqrt (2 * Real.pi * t))⁻¹) using 1
  · grind
  linarith
section
variable {t a : ℝ}
section
variable (ht : 0 < t)
include ht

private theorem integrableOn_mul_brownianHeatDensity_translate :
    IntegrableOn (fun y : ℝ => (y + a) * brownianHeatDensity t (y + a))
      (Set.Ioi 0) (volume : Measure ℝ) :=
  (integrable_mul_brownianHeatDensity_translate ht).integrableOn

/-- A Gaussian first-moment tail is its heat-kernel boundary value. -/
private theorem integral_brownianHeatDensity_linear_tail :
    ∫ y in Set.Ioi 0, (y + a) * brownianHeatDensity t (y + a)
      ∂(volume : Measure ℝ) = t * brownianHeatDensity t a := by
  let F : ℝ → ℝ := fun y => -t * brownianHeatDensity t (y + a)
  have hderiv : ∀ y ∈ Set.Ici 0,
      HasDerivAt F ((y + a) * brownianHeatDensity t (y + a)) y := by
    intro y hy
    have hF := ((brownianHeatDensity_hasDerivAt ht).comp y ((hasDerivAt_id y).add_const a)).const_mul (-t)
    grind
  have harg : Tendsto (fun y => -((y + a) ^ 2) / (2 * t)) atTop atBot := by
    have hpow : Tendsto (fun y => (y + a) ^ 2) atTop atTop := by
      refine Filter.tendsto_atTop.2 ?_
      intro b
      refine Filter.eventually_atTop.2 ⟨max 1 b - a, ?_⟩
      intro y hy
      have h1 : 1 ≤ y + a := by simp_all
      have hb : b ≤ y + a := by simp_all
      nlinarith
    have hcoef : 0 < 1 / (2 * t) := by positivity
    have hscale := hpow.const_mul_atTop_of_neg (neg_lt_zero.mpr hcoef)
    grind
  have hqtendsto : Tendsto (fun y => brownianHeatDensity t (y + a)) atTop (𝓝 0) := by
    have hsqrt : 0 < Real.sqrt (2 * Real.pi * t) := by positivity
    simpa [brownianHeatDensity, ht, div_eq_mul_inv, mul_comm] using
      (Real.tendsto_exp_atBot.comp harg).const_mul ((Real.sqrt (2 * Real.pi * t))⁻¹)
  have hF_tendsto : Tendsto F atTop (𝓝 0) := by
    simpa [F] using hqtendsto.const_mul (-t)
  have hint := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrableOn_mul_brownianHeatDensity_translate ht) hF_tendsto
  aesop

private theorem integrableOn_brownianHeatDensity_translate :
    IntegrableOn (fun y : ℝ => brownianHeatDensity t (y + a))
      (Set.Ioi 0) (volume : Measure ℝ) :=
  (DOZZ.Proofs.integrable_brownianHeatDensity_translate ht).integrableOn

end

end

/-- The BES(3) Doob transition density has unit mass on the positive half-line. -/
theorem conditionedPositiveTransitionDensity_integral_eq_one_zero
    {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    ∫ y in Set.Ioi 0, conditionedPositiveTransitionDensity 0 t x y
      ∂(volume : Measure ℝ) = 1 := by
  have hfirst :
      (∫ y in Set.Ioi 0, y *
          (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x))
          ∂volume) = x := by
    have hlin :
        (∫ y in Set.Ioi 0,
          ((y - x) * brownianHeatDensity t (y - x) -
            (y + x) * brownianHeatDensity t (y + x) +
            x * (brownianHeatDensity t (y - x) + brownianHeatDensity t (y + x)))
          ∂volume) = x := by
      have hleft := integral_brownianHeatDensity_linear_tail (t := t) (a := -x) ht
      have hA : IntegrableOn (fun y : ℝ => (y - x) * brownianHeatDensity t (y - x))
          (Set.Ioi 0) volume := by
        simpa only [sub_eq_add_neg] using
          integrableOn_mul_brownianHeatDensity_translate (t := t) (a := -x) ht
      have hB := integrableOn_mul_brownianHeatDensity_translate (t := t) (a := x) ht
      have hqA : IntegrableOn (fun y : ℝ => brownianHeatDensity t (y - x))
          (Set.Ioi 0) volume := by
        simpa only [sub_eq_add_neg] using
          integrableOn_brownianHeatDensity_translate (t := t) (a := -x) ht
      have hqB := integrableOn_brownianHeatDensity_translate (t := t) (a := x) ht
      have hsumInt := hqA.add hqB
      have hsumMul :=
        hsumInt.integrable.const_mul x
      have hleft' :
          ∫ y in Set.Ioi 0, (y - x) * brownianHeatDensity t (y - x)
            ∂volume = t * brownianHeatDensity t (-x) := by
        assumption
      calc
        _ = ∫ y in Set.Ioi 0,
              ((y - x) * brownianHeatDensity t _ -
                (y + x) * brownianHeatDensity t _ +
                x * (brownianHeatDensity t _ + brownianHeatDensity t _))
              ∂volume := by
            rfl
        _ = (∫ y in Set.Ioi 0, (y - x) * brownianHeatDensity t _
                ∂volume) -
              ∫ y in Set.Ioi 0, (y + x) * brownianHeatDensity t _
                ∂volume +
              x * (∫ y in Set.Ioi 0,
                brownianHeatDensity t _ + brownianHeatDensity t (y + x)
                ∂volume) := by
            calc
              _ = (∫ y in Set.Ioi 0,
                    (y - x) * brownianHeatDensity t _ -
                      (y + x) * brownianHeatDensity t _
                    ∂volume) +
                  ∫ y in Set.Ioi 0,
                    x * (brownianHeatDensity t (y - x) + brownianHeatDensity t (y + x))
                    ∂volume :=
                  integral_add (hA.sub hB) hsumMul
              _ = _ := by
                  rw [integral_sub hA hB, integral_const_mul]
        _ = t * brownianHeatDensity t (-x) - t * brownianHeatDensity t x + x * 1 := by
            rw [hleft', (integral_brownianHeatDensity_linear_tail (t := t) (a := x) ht), integral_add hqA hqB, (integral_brownianHeatDensity_halfline_pair (t := t) (a := x) ht)]
        _ = x := by
            have heven : brownianHeatDensity t (-x) = brownianHeatDensity t x := by
              simp [brownianHeatDensity, ht]
            simp_all
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
        ∂volume) = 1 := by
    rw [show (fun y : ℝ => (y / x) *
        (brownianHeatDensity t _ - brownianHeatDensity t _)) =
        fun y => x⁻¹ * (y *
          (brownianHeatDensity t _ - brownianHeatDensity t (y + x))) by
          funext y
          field_simp [hx.ne']]
    rw [integral_const_mul, hfirst]
    field_simp [hx.ne']
  rw [setIntegral_congr_fun measurableSet_Ioi]
  · exact hscale
  · assumption

end DOZZ.Proofs

end
