/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Tactic.Linarith

/-! Tail comparison by a positive extended-real remainder. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem ennreal_tail_domination
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (A B E : Ω → ℝ≥0∞) (hcomp : ∀ᵐ ω ∂P, A ω ≤ B ω+E ω)
    (x h : ℝ) (hh : 0 ≤ h) (hhx : h ≤ x) :
    (P {ω | ENNReal.ofReal x < A ω}).toReal ≤
      (P {ω | ENNReal.ofReal (x-h) < B ω}).toReal+
        (P {ω | ENNReal.ofReal h < E ω}).toReal := by
  have hsub : {ω | ENNReal.ofReal x < A ω} ≤ᵐ[P]
      {ω | ENNReal.ofReal (x-h) < B ω} ∪ {ω | ENNReal.ofReal h < E ω} := by
    filter_upwards [hcomp] with ω hω
    intro hx
    by_cases hb : ENNReal.ofReal (x-h) < B ω
    · simp_all
    by_cases he : ENNReal.ofReal h < E ω
    · simp_all
    · have hsum : B ω+E ω ≤ ENNReal.ofReal x := by
        calc B ω+E ω ≤ ENNReal.ofReal _+ENNReal.ofReal h :=
              add_le_add (le_of_not_gt hb) (le_of_not_gt he)
          _ = ENNReal.ofReal x := by
              rw [← ENNReal.ofReal_add (sub_nonneg.mpr hhx) hh,sub_add_cancel]
      grind
  have ht := ENNReal.toReal_mono (by finiteness) ((measure_mono_ae hsub).trans (measure_union_le ..))
  rwa [ENNReal.toReal_add (by finiteness) (by finiteness)] at ht

end DOZZ.Proofs
