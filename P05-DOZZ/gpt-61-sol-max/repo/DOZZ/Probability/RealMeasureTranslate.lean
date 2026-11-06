/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Algebra.Order.Group.Pointwise.Interval
/-! Translation preserves finiteness on real compact intervals. -/
public section
open MeasureTheory Set
namespace DOZZ.Proofs

theorem realMeasure_map_sub_Icc_lt_top {μ : Measure ℝ}
    (hμ : ∀ a b : ℝ, μ (Icc a b) < ⊤) (T a b : ℝ) :
    μ.map (fun s => s - T) (Icc a b) < ⊤ := by
  rw [Measure.map_apply (show Measurable (fun s : ℝ => s - T) from
    measurable_id.sub_const T) measurableSet_Icc]
  simpa only [preimage_sub_const_Icc] using hμ (a + T) (b + T)

end DOZZ.Proofs
