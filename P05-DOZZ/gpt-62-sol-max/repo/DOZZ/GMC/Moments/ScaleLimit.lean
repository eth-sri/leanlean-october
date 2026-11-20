/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Prod
public import DOZZ.GMC.ConvergenceInMeasure

/-! Convergence in measure is stable under an independent finite scalar multiplier. -/

@[expose] public section

open MeasureTheory Filter Topology

namespace DOZZ.Proofs

/-- Multiplying a sequence converging in measure by a finite random scalar on an independent
product space preserves convergence in measure. The proof truncates the scalar and controls its
tail using continuity from above for a finite measure. -/
theorem tendstoInMeasure_mul_snd_of_tendstoInMeasure
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ) (W : Ω' → ℝ)
    (hW : Measurable W) (hfg : TendstoInMeasure P f atTop g) :
    TendstoInMeasure (P.prod Q) (fun n p => W p.2 * f n p.1)
      atTop (fun p => W p.2 * g p.1) :=
  tendstoInMeasure_mul_random (hW.comp measurable_snd).aemeasurable (by
    rw [tendstoInMeasure_iff_norm] at hfg ⊢
    intro ε hε
    have he (i : ℕ) : {x : Ω × Ω' | ε ≤ ‖f i x.1 - g x.1‖} =
        {x : Ω | ε ≤ ‖f i x - g x‖} ×ˢ Set.univ := by ext x; simp
    simpa only [he, Measure.prod_prod, measure_univ, mul_one] using hfg ε hε)

end DOZZ.Proofs
