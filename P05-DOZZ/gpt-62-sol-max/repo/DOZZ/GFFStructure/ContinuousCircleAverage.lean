/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsCircleAverage

/-! Jointly measurable, sample-continuous representatives of the circle average. -/
@[expose] public section

open MeasureTheory
namespace DOZZ

structure IsContinuousCircleAverage {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ) : Prop where
  isCircleAverage : IsCircleAverage P X Xc
  measurable : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2)
  continuous_ae : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)

end DOZZ
