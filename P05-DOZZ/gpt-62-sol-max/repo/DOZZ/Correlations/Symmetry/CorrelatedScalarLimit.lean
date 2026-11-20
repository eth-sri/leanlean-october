/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Prod
public import DOZZ.GMC.ConvergenceInMeasure
@[expose] public section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace DOZZ.Proofs

/-- A finite correlated scalar preserves convergence in probability. No independence is used. -/
theorem tendstoInMeasure_mul_same_space
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {l : Filter ι} (f : ι → Ω → ℝ) (g W : Ω → ℝ)
    (hW : Measurable W) (hfg : TendstoInMeasure P f l g) :
    TendstoInMeasure P (fun i ω => W ω * f i ω) l (fun ω => W ω * g ω) :=
  tendstoInMeasure_mul_random hW.aemeasurable hfg

end DOZZ.Proofs
