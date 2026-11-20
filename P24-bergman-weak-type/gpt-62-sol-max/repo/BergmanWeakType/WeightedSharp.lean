/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.WeightedPotential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
public import BergmanWeakType.Weighted.MassCoordinate
public import BergmanWeakType.Weighted.AnnularSharpness
public import BergmanWeakType.WeakType
public import BergmanWeakType.Boundary.Concentration

/-! # Sharp positive weighted constants and the complex weighted upper bound -/

public section

open MeasureTheory Set Real Filter

namespace BergmanWeakType

open Weighted

/-- A lower bound on backward secant slopes is a lower bound on the derivative a.e. -/
private theorem integral_le_of_slope_domination {A G : ℝ → ℝ} {M : ℝ}
    (hn : ∀ y ∈ openRadii, 0 ≤ A y)
    (hG : ∀ y ∈ openRadii, G y ∈ Icc 0 M)
    (hs : ∀ x ∈ openRadii, ∀ y ∈ openRadii, x < y → A y ≤ slope G x y) :
    (∫ y in (0 : ℝ)..1, A y) ≤ M := by
  let F (x : ℝ) := if x ≤ 0 then 0 else if 1 ≤ x then M else G x
  have hM : 0 ≤ M := by have := hG (1 / 2) (by norm_num); grind
  have hm' : MonotoneOn G (openRadii) := by
    intro x hx y hy h
    rcases h.eq_or_lt with rfl | h
    · rfl
    exact (slope_nonneg_iff_of_le h.le).mp ((hn y hy).trans (hs x hx y hy h))
  have hm : Monotone F := by intro x y h; grind [MonotoneOn]
  have h := hm.monotoneOn (uIcc (0 : ℝ) 1)
  calc
    _ ≤ ∫ y in (0 : ℝ)..1, deriv F y := by
      simp only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      refine integral_mono_of_nonneg ((ae_restrict_mem measurableSet_Ioo).mono hn)
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp h.intervalIntegrable_deriv) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hm.ae_differentiableAt] with y hy hdy
      apply ge_of_tendsto (hdy.hasDerivAt.tendsto_slope.mono_left (nhdsLT_le_nhdsNE y))
      filter_upwards [Ioo_mem_nhdsLT hy.1] with x hx
      have hx' : x ∈ openRadii := ⟨hx.1, hx.2.trans hy.2⟩
      rw [slope_comm F y x]
      simpa [slope, F, hy.1.not_ge, hy.2.not_ge, hx'.1.not_ge, hx'.2.not_ge] using hs x hx' y hy hx.2
    _ ≤ M := by
      have he := h.intervalIntegral_deriv_mem_uIcc
      rw [show F 1 - F 0 = M by norm_num [F], uIcc_of_le hM] at he
      exact he.2

/-- The sharp positive weighted weak type bound for every admissible standard weight. -/
theorem isWeakTypeBound_weightedPositiveProjection {α : ℝ} (hα : -1 < α) :
    IsWeakTypeBound (weightedArea α) (weightedPositiveProjection α)
      (ENNReal.ofReal (gammaConstant α)) := by
  let := weightedArea_isProbabilityMeasure α hα
  intro f hf t ht
  let μ := weightedArea α
  let U := weightedDiskPotential α f
  let V := fun y θ ↦ U (massMap α (y, θ))
  let s := t / gammaConstant α
  let S := {z : ℂ | s * radiusMass α ‖z‖ < U z}
  have hγ := gammaConstant_pos hα
  have hs : 0 ≤ s := div_nonneg ht.le hγ.le
  have hU := measurable_weightedDiskPotential hf
  have hS : MeasurableSet S := measurableSet_lt (by fun_prop) hU
  have hr {y : ℝ} (hy : y ∈ openRadii) := Ioo_subset_Ico_self (massRadius_mem_unit hα hy)
  let A y := s * ∫ θ, (if s * y < V y θ then (1 : ℝ) else 0) ∂angleMeasure
  have hi : s * μ.real S ≤ ∫ w, ‖f w‖ ∂μ := by
    calc
      _ = ∫ y in (0 : ℝ)..1, A y := by
        rw [← integral_indicator_one hS, integral_weightedArea_mass hα ((integrable_const _).indicator hS),
          ← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
        intro y hy
        simp [A, circleAverage_eq_integral_angleMeasure, V, S, Set.indicator,
          abs_of_nonneg (hr hy).1, massRadius_mass hα hy]
      _ ≤ _ := by
        let G y := angularMean (fun r θ ↦ min (V r θ) (s * y)) y
        have hu y θ := weightedDiskPotential_nonneg α f (massMap α (y, θ))
        have hcap (y c : ℝ) : Integrable (fun θ ↦ min (V y θ) c) angleMeasure :=
          Integrable.of_bound (((hU.comp ((measurable_massMap α).comp measurable_prodMk_left)).inf
            measurable_const).aestronglyMeasurable) |c| (.of_forall fun θ ↦ by simp_all; grind)
        apply integral_le_of_slope_domination (G := G)
        · exact fun y _ ↦ mul_nonneg hs (integral_nonneg fun θ ↦ by positivity)
        · exact fun y hy ↦ ⟨integral_nonneg fun θ ↦ le_min (hu y θ) (mul_nonneg hs hy.1.le),
            angularMean_cap_le_mass hf (hr hy) _⟩
        intro y hy u hu' hyu
        rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hyu)]
        have hinc := integral_mono_of_nonneg (f := fun θ ↦ ((u - y) * s) *
            (if s * u < V u θ then (1 : ℝ) else 0)) (.of_forall fun θ ↦ by positivity)
          ((hcap u (s * u)).sub (hcap u (s * y))) (.of_forall fun θ ↦ by norm_num [*]; grind)
        rw [integral_const_mul, integral_sub' (hcap _ _) (hcap _ _)] at hinc
        have hm := (antitoneOn_angularMean_cap hf (s * y)) (hr hu') (hr hy)
          ((massRadius_strictAntiOn hα).antitoneOn hy hu' hyu.le)
        dsimp [A, G, angularMean, V] at *
        nlinarith
  let E := {z | ENNReal.ofReal t < weightedPositiveProjection α f z}
  have hm : μ E ≤ μ S := by
    apply measure_mono_ae
    filter_upwards [ae_mem_disk_weightedArea α] with z hz hlev
    have hz1 := (mem_disk_iff z).mp hz
    have hF : t < weightedPotential α f z := by
      apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mp
      have hi : Integrable (fun w ↦ weightedKernel α z w * f w) μ :=
        hf.mul_of_top_right (memLp_weightedKernel_top hz)
      have h := ofReal_integral_norm_eq_lintegral_enorm hi
      simp only [norm_mul] at h
      rw [weightedPotential_eq_norm_mul hf, h]
      simpa only [E, mem_ofPred_eq, weightedPositiveProjection, ofReal_norm, ← enorm_mul] using hlev
    change s * radiusMass α ‖z‖ < U z
    change _ < weightedDiskPotential α f z
    rw [weightedDiskPotential, lt_div_iff₀ (normalizer_pos α ⟨norm_nonneg z, hz1⟩)]
    calc
      _ ≤ s * gammaConstant α := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (radialMass_mul_normalizer_le hα (norm_nonneg z) hz1) hs
      _ = t := div_mul_cancel₀ t hγ.ne'
      _ < _ := hF
  change ENNReal.ofReal t * μ E ≤ _
  rw [← ofReal_integral_norm_eq_lintegral_enorm hf, ← ENNReal.ofReal_mul hγ.le,
    ← ENNReal.ofReal_toReal (measure_ne_top μ E), ← ENNReal.ofReal_mul ht.le]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_comm (gammaConstant α), ← div_le_iff₀ hγ, mul_div_right_comm]
  exact (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top _ _) hm) hs).trans hi

theorem weightedPositiveProjection_constant_eq (α : ℝ) (hα : -1 < α) :
    weakTypeConstant (weightedArea α) (weightedPositiveProjection α) =
      ENNReal.ofReal (gammaConstant α) :=
  le_antisymm (sInf_le (isWeakTypeBound_weightedPositiveProjection hα))
    (gammaConstant_le_weightedPositiveProjection_constant α hα)

theorem weightedProjection_constant_le (α : ℝ) (hα : -1 < α) :
    weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) ≤
      ENNReal.ofReal (gammaConstant α) := by
  rw [← weightedPositiveProjection_constant_eq α hα]
  apply sInf_le_sInf
  intro C hC f hf t ht
  refine le_trans (mul_le_mul_right (measure_mono fun z hz ↦ ?_) _) (hC f hf t ht)
  exact hz.trans_le (enorm_weightedProjection_le_weightedPositiveProjection α f z)

theorem positiveProjection_constant_eq_one : weakTypeConstant diskArea positiveProjection = 1 := by
  simpa using weightedPositiveProjection_constant_eq 0 (by norm_num)

theorem projection_constant_eq_one :
    weakTypeConstant diskArea (fun f z ↦ ‖projection f z‖ₑ) = 1 :=
  le_antisymm (by simpa using weightedProjection_constant_le 0 (by norm_num))
    (by simpa using one_le_weightedProjection_constant 0 (by norm_num))

end BergmanWeakType
