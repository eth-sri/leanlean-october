/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Linarith

/-! Event bounds for the sum of two possibly dependent positive masses. -/

open MeasureTheory Set

namespace DOZZ.Proofs

theorem two_mass_tail_sandwich
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (A B : Ω → ℝ) (hB : AEMeasurable B P)
    (hA0 : ∀ ω, 0 ≤ A ω) (hB0 : ∀ ω, 0 ≤ B ω) (x h : ℝ) :
    P.real {ω | x < A ω} + P.real {ω | x < B ω} -
      P.real {ω | x < A ω ∧ x < B ω} ≤ P.real {ω | x < A ω+B ω} ∧
    P.real {ω | x < A ω+B ω} ≤
      P.real {ω | x-h < A ω} + P.real {ω | x-h < B ω} +
        P.real {ω | h < A ω ∧ h < B ω} := by
  constructor
  · have hi : {ω | x < A ω} ∪ {ω | x < B ω} ⊆ {ω | x < A ω+B ω} := by
      intro ω hω
      rcases hω with hω | hω
      · exact lt_of_lt_of_le hω (le_add_of_nonneg_right (hB0 ω))
      · exact lt_of_lt_of_le hω (le_add_of_nonneg_left (hA0 ω))
    have hm := measureReal_mono hi (μ := P)
    have hu := measureReal_union_add_inter₀ (μ := P)
      (s := {ω | x < A ω}) (nullMeasurableSet_lt aemeasurable_const hB)
    change P.real ({ω | x < A ω} ∪ {ω | x < B ω}) +
      P.real {ω | x < A ω ∧ x < B ω} = _ at hu
    linarith only [hm,hu]
  · have hi : {ω | x < A ω+B ω} ⊆
        ({ω | x-h < A ω} ∪ {ω | x-h < B ω}) ∪ {ω | h < A ω ∧ h < B ω} := by
      intro ω hω
      by_cases ha : x-h < A ω
      · exact Or.inl (Or.inl ha)
      by_cases hb : x-h < B ω
      · exact Or.inl (Or.inr hb)
      · exact Or.inr ⟨by dsimp at *; linarith, by dsimp at *; linarith⟩
    have hm := measureReal_mono hi (μ := P)
    have h1 := measureReal_union_le (μ := P)
      ({ω | x-h < A ω} ∪ {ω | x-h < B ω}) {ω | h < A ω ∧ h < B ω}
    have h2 := measureReal_union_le (μ := P) {ω | x-h < A ω} {ω | x-h < B ω}
    linarith only [hm,h1,h2]

end DOZZ.Proofs
