/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! Fixed integrable changes of measure preserve convergence in measure. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

/-- Convergence in measure is preserved by a fixed integrable density. This is the fixed-size
tilt passage needed when a GMC cutoff converges under a Gaussian change of measure. -/
theorem tendstoInMeasure_withDensity_of_lintegral_lt_top
    {α ι E : Type*} [MeasurableSpace α] [MeasurableSpace E]
    [PseudoEMetricSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure α} {l : Filter ι} {f : ι → α → E} {g : α → E}
    (ρ : α → ℝ≥0∞) (hρ : ∫⁻ x, ρ x ∂μ < ∞)
    (hf : ∀ i, Measurable (f i)) (hg : Measurable g)
    (hconv : TendstoInMeasure μ f l g) :
    TendstoInMeasure (μ.withDensity ρ) f l g := by
  intro ε hε
  have hset (i : ι) : MeasurableSet {x | ε ≤ edist (f i x) (g x)} := by measurability
  have hweighted := tendsto_setLIntegral_zero (ne_of_lt hρ) (hconv ε hε)
  simp_all

end DOZZ.Proofs
