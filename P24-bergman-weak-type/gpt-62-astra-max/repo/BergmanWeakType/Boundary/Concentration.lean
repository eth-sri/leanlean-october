/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Measure
public import BergmanWeakType.WeakType
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Interior kernel columns as limits of admissible inputs -/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal Topology

namespace BergmanWeakType

/-- A point column is a limiting probability source, even for a point on the
boundary. -/
theorem column_test {α L : ℝ} (hα : -1 < α)
    {a : ℂ} (ha : a ∈ ClosedDisk) {E : Set ℂ} (hmE : MeasurableSet E) (hE : E ⊆ disk)
    (hcol : ∀ z ∈ E, L ≤ ‖weightedKernel α z a‖) (hL : 0 < L) :
    ENNReal.ofReal L * weightedArea α E ≤ weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) := by
  apply test_source hα _ (kernel_continuous α) (by unfold weightedKernel; fun_prop) _ (Measure.dirac ⟨a,ha⟩) hmE hE hL
  · simp_all
  · intro f z; simp [mul_comm]
    rfl

theorem one_le_weightedProjection_constant (α : ℝ) (hα : -1 < α) :
    1 ≤ weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) := by
  let := weightedArea_isProbabilityMeasure α hα
  have hd : weightedArea α disk = 1 := (measure_congr (ae_eq_univ.mpr (ae_mem_disk_weightedArea α))).trans (measure_univ)
  simpa [hd] using column_test hα (a := 0) (by simp) measurableSet_disk Subset.rfl
     (by simp) zero_lt_one

end BergmanWeakType
