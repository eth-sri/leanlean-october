/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Tactic.Module
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import BergmanWeakType.PolarMeasure
public import BergmanWeakType.Kernel
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Normalization and support of Bergman area measures -/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BergmanWeakType

instance diskArea_isProbabilityMeasure : IsProbabilityMeasure diskArea := by
  simpa using weightedArea_isProbabilityMeasure 0 (by norm_num)

theorem ae_mem_disk : ∀ᵐ z ∂diskArea, z ∈ disk :=
  ae_restrict_mem Metric.isOpen_ball.measurableSet

theorem ae_mem_disk_weightedArea (α : ℝ) : ∀ᵐ z ∂weightedArea α, z ∈ disk := (withDensity_absolutelyContinuous diskArea _).ae_le ae_mem_disk

/-- The admissible radial weights have the same null sets as disk area. -/
theorem diskArea_absolutelyContinuous_weightedArea (α : ℝ) (hα : -1 < α) :
    diskArea ≪ weightedArea α := by
  apply withDensity_absolutelyContinuous'
  · fun_prop
  · filter_upwards [ae_mem_disk] with z hz
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    apply mul_pos (by linarith)
    apply Real.rpow_pos_of_pos
    simp_all

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem disk_polar {f : ℂ → E} (hf : Integrable f diskArea) :
    ∫ z, f z ∂diskArea = ∫ r, Real.circleAverage f 0 r ∂radialLaw 0 := by
  simpa using weighted_polar (α := 0) (by norm_num) (by simpa using hf)

end BergmanWeakType
