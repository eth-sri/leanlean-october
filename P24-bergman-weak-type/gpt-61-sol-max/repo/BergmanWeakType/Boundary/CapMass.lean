/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Boundary.Concentration
import BergmanWeakType.Boundary.HalfDiskIntegral
import BergmanWeakType.Weighted.PolarIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic
import BergmanWeakType.RpowRing

variable {R α : ℝ}

/-! # The mass of small caps at the boundary of the disk -/



noncomputable section

open MeasureTheory
open scoped Topology

namespace BergmanWeakType

def capProfile (α R : ℝ) (u : ℂ) : ℝ :=
  max (2 * u.re - R * ‖u‖ ^ 2) 0 ^ α

theorem norm_sq_boundary_affine (R : ℝ) (u ) :
    ‖1 - (R : ℂ) * u‖ ^ 2 = 1 - 2 * R * u.re + R ^ 2 * ‖u‖ ^ 2 := by
  simp_all [Complex.sq_norm, Complex.normSq_apply] <;> nlinarith

theorem boundary_affine_mem_cap  (hR : 0 < R) (u ) :
    1 - (R : ℂ) * u ∈ boundaryCap R ↔ u ∈ disk ∧ R * ‖u‖ ^ 2 < 2 * u.re := by
  have hid := norm_sq_boundary_affine R u
  simp_all [boundaryCap, Metric.mem_ball, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
  aesop (add safe (by nlinarith [norm_nonneg (1 - R * u)]))

theorem weightedArea_boundaryCap_rescaled (hα : 0 < α) (hR : 0 < R) :
    R ^ (-(α + 2)) * (weightedArea α).real (boundaryCap R) = (α + 1) * ∫ u, capProfile α R u ∂diskArea :=
  by
  conv_lhs =>
    arg 2
    equals (α + 1) * ∫ z, (boundaryCap R).indicator (fun z ↦ (1 - ‖z‖ ^ 2) ^ α) z ∂area =>
      rw [← integral_indicator_one (s := boundaryCap R) (measurableSet_disk.inter Metric.isOpen_ball.measurableSet),
        integral_weightedArea_eq_diskArea (by linarith : -1 < α), diskArea,
        ← integral_indicator measurableSet_disk, ← integral_const_mul]
      congr 1
      ext z
      simp +contextual [boundaryCap, Set.indicator, radialDensity, ite_and]
  have heq :=
    Measure.integral_comp_smul_of_nonneg area
      (fun z : ℂ ↦ (boundaryCap R).indicator (fun z ↦ (1 - ‖z‖ ^ 2) ^ α) (1 - z)) R (hR := hR.le)
  simp [integral_sub_left_eq_self] at heq
  conv_lhs at heq =>
    enter [2, u]
    equals R ^ α * disk.indicator (capProfile α R) u =>
      by_cases hu : u ∈ disk <;>
        simp [Set.indicator, boundary_affine_mem_cap hR, hu]
      dsimp [capProfile]
      by_cases hp : R * ‖u‖ ^ 2 < 2 * u.re
      · rw [ite_eq_left hp, max_eq_left (by linarith), norm_sq_boundary_affine]
        convert Real.mul_rpow hR.le (by linarith : 0 ≤ 2 * u.re - R * ‖u‖ ^ 2) (z := α)
          using 1 <;> congr 1 <;> ring
      · rw [ite_eq_right hp, max_eq_right (by linarith), Real.zero_rpow hα.ne', mul_zero]
  rw [integral_const_mul, integral_indicator measurableSet_disk] at heq
  have hp : R ^ (-(α + 2)) * R ^ α * R ^ 2 = 1 := by rpow_ring
  change R ^ α * ∫ u, capProfile α R u ∂diskArea = _ at heq
  grind

theorem tendsto_integral_capProfile (hα : 0 < α) :
    Filter.Tendsto (fun R ↦ ∫ u, capProfile α R u ∂diskArea) (𝓝[>] 0) (𝓝 (gammaConstant α / (α + 2))) :=
  by
  rw [← integral_halfDiskPower hα]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ 2 ^ α)
  · apply Filter.Eventually.of_forall
    intro R
    fun_prop (disch := positivity) [capProfile]
  · filter_upwards [self_mem_nhdsWithin] with R hR
    filter_upwards [ae_mem_disk] with u hu
    unfold capProfile
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_max_right _ _) _)]
    apply Real.rpow_le_rpow (le_max_right _ _) _ hα.le
    apply max_le _ zero_le_two
    have := (mem_disk_iff u).mp hu
    nlinarith [Complex.re_le_norm u, mul_nonneg hR.le (sq_nonneg ‖u‖)]
  · simp_all
  · apply Filter.Eventually.of_forall
    intro u
    have hc : Continuous (fun R : ℝ ↦ capProfile α R u) :=
      by
      unfold capProfile
      fun_prop (disch := positivity)
    simpa [capProfile, halfDiskPower] using!
      hc.continuousAt.tendsto.mono_left (show 𝓝[>] 0 ≤ 𝓝 0 from nhdsWithin_le_nhds)


end BergmanWeakType
