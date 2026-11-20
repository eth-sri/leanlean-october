/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsAdmissibleGMCVersion
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Modify a random measure on a null set so it is finite at every outcome. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- An almost surely finite measurable random measure has a measurable representative that is
finite for every outcome and agrees with the original random measure almost surely. -/
theorem exists_everywhere_finite_measure_version
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) (hM : Measurable M)
    (hfinite : ∀ᵐ ω ∂P, IsFiniteMeasure (M ω)) :
    ∃ N : Ω → Measure ℂ,
      Measurable N ∧ (∀ ω, IsFiniteMeasure (N ω)) ∧ ∀ᵐ ω ∂P, N ω = M ω := by
  classical
  let good  := {ω | M ω Set.univ < ∞}
  have hEval  :=
    (Measure.measurable_coe MeasurableSet.univ).comp hM
  have hgood : MeasurableSet good := by
    dsimp [good]
    measurability
  let N  := fun ω => if ω ∈ good then M ω else 0
  have hN : Measurable N := Measurable.ite hgood hM measurable_const
  refine ⟨N, hN, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ good
    · have hmass : M ω Set.univ < ∞ := by simpa [good] using hω
      exact ⟨by simpa [N, hω] using hmass⟩
    · have hzero : IsFiniteMeasure (0 : Measure ℂ) := ⟨by simp⟩
      simpa [N, hω] using hzero
  · filter_upwards [hfinite] with ω hω
    have hmass  := hω.measure_univ_lt_top
    simp [N, good, hmass]

end DOZZ.Proofs
