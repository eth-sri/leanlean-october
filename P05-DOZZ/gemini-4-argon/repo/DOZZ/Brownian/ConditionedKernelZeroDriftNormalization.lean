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

theorem integrable_mul_brownianHeatDensity {t} (ht : 0 < t) :
    Integrable (fun z : ℝ => z * brownianHeatDensity t z) (volume : Measure ℝ) := by
  have hcoef : 0 < 1 / (2 * t) := by positivity
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * t) := by positivity
  refine ((integrable_mul_exp_neg_mul_sq hcoef).mul_const ((Real.sqrt (2 * Real.pi * t))⁻¹)).congr ?_
  filter_upwards [] with z
  have hq : brownianHeatDensity t z =
      Real.exp (-(1 / (2 * t)) * z ^ 2) * (Real.sqrt (2 * Real.pi * t))⁻¹ := by
    simp only [brownianHeatDensity, ite_eq_left ht]
    rw [div_eq_mul_inv]
    congr 1
    field_simp [ht.ne', hsqrt.ne']
  rw [hq]
  ring

private theorem integrable_mul_brownianHeatDensity_translate {t a} (ht : 0 < t) :
    Integrable (fun y : ℝ => (y + a) * brownianHeatDensity t (y + a))
      (volume : Measure ℝ) := by
  exact ((Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding).integrable_map_iff.mp (show Integrable (fun z => z * brownianHeatDensity t z) ((volume : Measure ℝ).map (fun y => y + a)) by rw [(Measure.IsAddRightInvariant.map_add_right_eq_self a)]; exact integrable_mul_brownianHeatDensity ht)


private theorem integrableOn_mul_brownianHeatDensity_translate {t a} (ht : 0 < t) :
    IntegrableOn (fun y : ℝ => (y + a) * brownianHeatDensity t (y + a))
      (Set.Ioi 0) (volume : Measure ℝ) :=
  (integrable_mul_brownianHeatDensity_translate ht).integrableOn


private theorem integrable_brownianHeatDensity_translate_local {t a} (ht : 0 < t) :
    Integrable (fun y : ℝ => brownianHeatDensity t (y + a)) (volume : Measure ℝ) := by
  exact ((Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding).integrable_map_iff.mp (show Integrable (brownianHeatDensity t) ((volume : Measure ℝ).map (fun y => y + a)) by rw [(Measure.IsAddRightInvariant.map_add_right_eq_self a)]; exact integrable_brownianHeatDensity ht)

private theorem integrableOn_brownianHeatDensity_translate {t a} (ht : 0 < t) :
    IntegrableOn (fun y : ℝ => brownianHeatDensity t (y + a))
      (Set.Ioi 0) (volume : Measure ℝ) :=
  (integrable_brownianHeatDensity_translate_local ht).integrableOn

/-- The BES(3) Doob transition density has unit mass on the positive half-line. -/
theorem conditionedPositiveTransitionDensity_integral_eq_one_zero
    {t x} (ht : 0 < t) (hx : 0 < x) :
    ∫ y in Set.Ioi 0, conditionedPositiveTransitionDensity 0 t x y
      ∂(volume : Measure ℝ) = 1 := by
  have integral_brownianHeatDensity_linear_tail {t} {a} (ht : 0 < t) : ∫ y in Set.Ioi 0, (y + a) * brownianHeatDensity t (y + a) ∂(volume : Measure ℝ) = t * brownianHeatDensity t a := by
    have brownianHeatDensity_hasDerivAt {t} {z} (ht : 0 < t) : HasDerivAt (brownianHeatDensity t) (-(z / t) * brownianHeatDensity t z) z := by
      have harg : HasDerivAt (fun w => -(w ^ 2) / (2 * t)) (-(z / t)) z := by
        convert ((hasDerivAt_id z).pow 2).const_mul (-(1 / (2 * t))) using 1
        · funext w
          field_simp [ht.ne']
          rfl
        · field_simp [ht.ne']
          norm_num [id]
          ring
      rw [(show brownianHeatDensity t = fun w => Real.exp (-(w ^ 2) / (2 * t)) * (Real.sqrt (2 * Real.pi * t))⁻¹ by funext w; simp only [brownianHeatDensity, ite_eq_left ht, div_eq_mul_inv])]
      convert ((Real.hasDerivAt_exp _).comp z harg).const_mul ((Real.sqrt (2 * Real.pi * t))⁻¹) using 1
      · funext w
        simp only [Function.comp_apply]
        ring
      · field_simp [ht.ne', (show 0 < Real.sqrt (2 * Real.pi * t) by positivity).ne']
    let F : ℝ → ℝ := fun y => -t * brownianHeatDensity t (y + a)
    have hderiv : ∀ y ∈ Set.Ici 0,
        HasDerivAt F ((y + a) * brownianHeatDensity t (y + a)) y := by
      intro y hy
      have hshift : HasDerivAt (fun z : ℝ => z + a) 1 y := (hasDerivAt_id y).add_const a
      convert (((brownianHeatDensity_hasDerivAt (t := t) (z := y + a) ht).comp y hshift).const_mul (-t)) using 1
      · change (fun z => -t * brownianHeatDensity t (z + a)) = _
        rfl
      · field_simp [ht.ne']
    have harg : Tendsto (fun y => -((y + a) ^ 2) / (2 * t)) atTop atBot := by
      have hpow : Tendsto (fun y => (y + a) ^ 2) atTop atTop := by
        refine Filter.tendsto_atTop.2 ?_
        intro b
        refine Filter.eventually_atTop.2 ⟨max 1 b - a, ?_⟩
        intro y hy
        have h1 : 1 ≤ y + a := by have := le_max_left (1 : ℝ) b; linarith
        have : b ≤ y + a := by have := le_max_right (1 : ℝ) b; linarith
        have hz : 0 ≤ y + a := le_trans (by norm_num) h1
        have hprod : 0 ≤ (y + a) * (y + a - 1) := mul_nonneg hz (by linarith)
        nlinarith
      have hcoef : 0 < 1 / (2 * t) := by positivity
      convert (hpow.const_mul_atTop_of_neg (neg_lt_zero.mpr hcoef)) using 1
      field_simp [ht.ne']
    have hqtendsto : Tendsto (fun y => brownianHeatDensity t (y + a)) atTop (𝓝 0) := by
      have hexp := Real.tendsto_exp_atBot.comp harg
      simpa [brownianHeatDensity, ht, div_eq_mul_inv, mul_comm] using
        hexp.const_mul ((Real.sqrt (2 * Real.pi * t))⁻¹)
    have hF_tendsto : Tendsto F atTop (𝓝 0) := by
      simpa [F] using hqtendsto.const_mul (-t)
    simpa [F] using (integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_mul_brownianHeatDensity_translate ht) hF_tendsto)
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
      have hA : IntegrableOn (fun y => (y - x) * brownianHeatDensity t (y - x))
          (Set.Ioi 0) (volume : Measure ℝ) := by
        simpa only [sub_eq_add_neg] using
          integrableOn_mul_brownianHeatDensity_translate (t := t) (a := -x) ht
      have hB := integrableOn_mul_brownianHeatDensity_translate (t := t) (a := x) ht
      have hqA : IntegrableOn (fun y => brownianHeatDensity t (y - x))
          (Set.Ioi 0) (volume : Measure ℝ) := by
        simpa only [sub_eq_add_neg] using
          integrableOn_brownianHeatDensity_translate (t := t) (a := -x) ht
      have hqB := integrableOn_brownianHeatDensity_translate (t := t) (a := x) ht
      calc
        _ = ∫ y in Set.Ioi 0,
              ((y - x) * brownianHeatDensity t (y - x) -
                (y + x) * brownianHeatDensity t (y + x) +
                x * (brownianHeatDensity t (y - x) + brownianHeatDensity t (y + x)))
              ∂(volume : Measure ℝ) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro y hy
            ring
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
                  integral_add (hA.sub hB) ((hqA.add hqB).integrable.const_mul x)
              _ = _ := by
                  rw [integral_sub hA hB, integral_const_mul]
        _ = t * brownianHeatDensity t (-x) - t * brownianHeatDensity t x + x * 1 := by
            rw [(show ∫ y in Set.Ioi 0, (y - x) * brownianHeatDensity t (y - x) ∂(volume : Measure ℝ) = t * brownianHeatDensity t (-x) by simpa only [sub_eq_add_neg] using (integral_brownianHeatDensity_linear_tail (t := t) (a := -x) ht)), (integral_brownianHeatDensity_linear_tail (t := t) (a := x) ht), integral_add hqA hqB, (integral_brownianHeatDensity_halfline_pair (t := t) (a := x) ht)]
        _ = x := by
            rw [(show brownianHeatDensity t (-x) = brownianHeatDensity t x by simp [brownianHeatDensity, ht])]
            ring
    calc
      _ = ∫ y in Set.Ioi 0,
          ((y - x) * brownianHeatDensity t (y - x) -
            (y + x) * brownianHeatDensity t (y + x) +
            x * (brownianHeatDensity t (y - x) + brownianHeatDensity t (y + x)))
          ∂(volume : Measure ℝ) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro y hy
            ring
      _ = x := hlin
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
    rw [show (fun y => (y / x) *
        (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x))) =
        fun y => x⁻¹ * (y *
          (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x))) by
          funext y
          field_simp [hx.ne']]
    rw [integral_const_mul, hfirst]
    field_simp [hx.ne']
  rw [setIntegral_congr_fun measurableSet_Ioi]
  · exact hscale
  · intro y hy
    exact hkernel y hy

end DOZZ.Proofs

end
