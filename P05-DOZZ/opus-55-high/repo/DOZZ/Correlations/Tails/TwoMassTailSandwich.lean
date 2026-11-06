/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Tactic.Linarith

/-! Event bounds for the sum of two possibly dependent positive masses. -/

@[expose] public section
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
      grind
    have hu := measureReal_union_add_inter₀ (μ := P)
      (s := {ω | x < A ω}) (nullMeasurableSet_lt aemeasurable_const hB)
    change P.real ({ω | x < A ω} ∪ {ω | x < B ω}) +
      P.real {ω | x < A ω ∧ x < B ω} = _ at hu
    linarith only [(measureReal_mono hi (μ := P)),hu]
  · have hi : {ω | x < A ω+B ω} ⊆
        ({ω | x-h < A ω} ∪ {ω | x-h < B ω}) ∪ {ω | h < A ω ∧ h < B ω} := by
      intro ω hω
      by_cases ha : x-h < A ω
      · simp_all
      by_cases hb : x-h < B ω
      · simp_all
      · exact Or.inr ⟨by grind, by grind⟩
    have h1 := measureReal_union_le (μ := P)
      ({ω | x-h < A ω} ∪ {ω | x-h < B ω}) {ω | h < A ω ∧ h < B ω}
    linarith only [(measureReal_mono hi (μ := P)),h1,(measureReal_union_le (μ := P) {ω | x-h < A ω} {ω | x-h < B ω})]

end DOZZ.Proofs
