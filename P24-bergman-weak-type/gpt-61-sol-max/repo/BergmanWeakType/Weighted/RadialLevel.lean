/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.Prod
import BergmanWeakType.Definitions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import BergmanWeakType.Weighted.CompactIntegral
import Mathlib.Tactic

variable {M c t : ℝ} {U : ℂ → ℝ} {ρ : ℝ → ℝ}

/-! # Distribution estimates from increasing truncations in a radial mass coordinate -/



noncomputable section

open MeasureTheory Real Set


namespace BergmanWeakType.Weighted

def circleAverage_bound {g : ℂ → ℝ} (hg : Measurable g)
    (hbound : ∀ z, ‖g z‖ ≤ M) (r) :=
  let hi : CircleIntegrable g 0 r :=
    (intervalIntegrable_const (c := M)).mono_fun'
      (hg.comp (continuous_circleMap 0 r).measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ ↦ hbound _)

  And.intro hi (norm_circleAverage_le_circleAverage_norm.trans
    (circleAverage_mono_on_of_le_circle hi.norm (fun z _ ↦ hbound z)))

section
variable (U ρ)

def radialCapMean (y c : ℝ) : ℝ :=
  circleAverage (fun z ↦ min (U z) c) 0 (ρ y)

def radialLevelFraction (t y : ℝ) : ℝ :=
  circleAverage (fun z ↦ if t * y < U z then 1 else 0) 0 (ρ y)

end

variable (hU : Measurable U)
include hU

def radialLevel_bound (t y r) :=
  circleAverage_bound (g := fun z ↦ if t * y < U z then (1 : ℝ) else 0)
    (measurable_const.ite (measurableSet_lt measurable_const hU) measurable_const)
    (M := 1) (fun z ↦ by split_ifs <;> norm_num) r

def radialCap_bound (hUpos : ∀ z, 0 ≤ U z) (c r) :=
  circleAverage_bound (g := fun z ↦ min (U z) c) (hU.inf measurable_const)
    (M := |c|) (fun z ↦ by rw [Real.norm_eq_abs, abs_le]; grind) r

/-- Increasing cap means in the mass coordinate give the integrated level-set estimate. -/
theorem integral_mul_radialLevelFraction_le (hUpos : ∀ z, 0 ≤ U z)
       (hρ : Measurable ρ)
    (hmono : ∀ c, MonotoneOn (fun y ↦ radialCapMean U ρ y c) (unitIoo))
    (hbound : ∀ y ∈ unitIoo, ∀ c, radialCapMean U ρ y c ≤ M)
     (ht : 0 ≤ t) :
    (∫ y in 0..1, t * radialLevelFraction U ρ t y) ≤ M := by
  let A := fun y ↦ t * radialLevelFraction U ρ t y
  let G := fun y ↦ radialCapMean U ρ y (t * y)
  have hA a b : IntervalIntegrable A volume a b := by
    apply IntervalIntegrable.const_mul
    apply (intervalIntegrable_const (c := 1)).mono_fun' 
      (Measurable.aestronglyMeasurable (by
        apply measurable_circleAverage hρ
        apply Measurable.ite <;> measurability))
    exact Filter.Eventually.of_forall fun y ↦ (radialLevel_bound hU t y _).2
  have hG a b : IntervalIntegrable G volume a b := by
    refine ((continuous_const_mul t).norm.intervalIntegrable a b).mono_fun' 
      (Measurable.aestronglyMeasurable (by
        apply measurable_circleAverage hρ
        fun_prop)) ?_
    exact Filter.Eventually.of_forall fun y ↦ (radialCap_bound hU hUpos (t * y) _).2
  suffices hinner : ∀ u ∈ Ioo 0 (1 / 3 : ℝ), ∫ y in u + u..1 - u, A y ≤ M by
    have hc := intervalIntegral.continuous_primitive hA 0
    simpa only [zero_add, sub_zero] using le_on_closure hinner
      (((hc.comp (continuous_const.sub continuous_id)).sub (hc.comp (continuous_id.add continuous_id))).congr
        (fun u ↦ intervalIntegral.integral_interval_sub_left (hA 0 _) (hA 0 _))).continuousOn continuousOn_const
      (by norm_num [closure_Ioo] : (0 : ℝ) ∈ closure _)
  intro u hu'
  have hu := hu'.1
  let v := 1 - 2 * u
  have huv : u < v := by dsimp [v]; linarith [hu'.2]
  convert_to (∫ y in u + u..v + u, A y) ≤ M using 1
  · congr 1 <;> dsimp [v] <;> ring

  have habG := hG u v
  have hshG := hG (u + u) (v + u)
  have hGc  :=
    (IntervalIntegrable.comp_add_right_iff).mpr hshG
  have hi := intervalIntegral.integral_mono_on huv.le (((IntervalIntegrable.comp_add_right_iff).mpr (hA (u + u) (v + u))).const_mul u)
    (hGc.sub habG) (fun y hy ↦ by
      have hy' : y ∈ unitIoo := ⟨hu.trans_le hy.1, by linarith [hy.2]⟩
      have hyh' : y + u ∈ unitIoo := ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have hinc := circleAverage_mono
        ((radialLevel_bound hU t (y + u) (ρ (y + u))).1.const_smul (a := t * u))
        ((radialCap_bound hU hUpos (t * (y + u)) _).1.sub
          (radialCap_bound hU hUpos (t * y) _).1)
        (fun z _ ↦ by dsimp; split_ifs <;> simp_all <;> grind)
      rw [circleAverage_smul, circleAverage_sub
        (radialCap_bound hU hUpos _ _).1
        (radialCap_bound hU hUpos _ _).1] at hinc
      have hm := hmono (t * y) hy' hyh' (by linarith)
      grind [radialLevelFraction, radialCapMean, smul_eq_mul])
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hGc habG,
    intervalIntegral.integral_comp_add_right A, intervalIntegral.integral_comp_add_right G,
    intervalIntegral.integral_interval_sub_interval_comm' hshG habG (hG u (u + u)).symm] at hi
  have hlo : 0 ≤ ∫ y in u..u + u, G y :=
    intervalIntegral.integral_nonneg (by linarith) fun y hy ↦
      circleAverage_nonneg_of_nonneg fun z _ ↦ le_min (hUpos z) (mul_nonneg ht (hu.le.trans hy.1))
  have hui  := by
    calc
      _ ≤ ∫ _y in v..v + u, M :=
        intervalIntegral.integral_mono_on (by linarith) (hG v (v + u)) intervalIntegrable_const
          fun y hy ↦ hbound y ⟨by grind, hy.2.trans_lt (by dsimp [v]; linarith)⟩ _
      _ = u * M := by simp
  nlinarith

end BergmanWeakType.Weighted
