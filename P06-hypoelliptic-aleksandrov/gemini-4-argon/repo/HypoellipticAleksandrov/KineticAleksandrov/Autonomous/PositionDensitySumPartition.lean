module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlap
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! # Output-cell partition of the actual positive Green density -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/- Raising the positive norm to its exponent recovers the power integral. -/
theorem positionPositiveNorm_rpow {X : Type*} [MeasurableSpace X]
    (m : Measure X) (q : ℝ) (hq : 0 < q) (f : X → ℝ≥0∞) :
    positionPositiveNorm m q f ^ q = ∫⁻ z, f z ^ q ∂m := by
  rw [positionPositiveNorm, ← ENNReal.rpow_mul,
    one_div_mul_cancel hq.ne', ENNReal.rpow_one]

/- The output cells partition the region after the grid origin in the active interval. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
