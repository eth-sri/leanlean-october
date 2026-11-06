module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapRestriction
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapPartition
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapCells
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapMixture
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapSupport
import Mathlib.Tactic

/-! # Source time-position overlap convolution for canonical active Green mixtures

Source: companion paper, Section 8. Constants are selected before coefficients, clocks,
starting measures, translated grids, and output cells.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal Classical

/- The literal exponential delay and finite-speed position overlap kernel. -/
def positionOverlapWeight (c₀ : ℝ) (i j : ℕ) (ell k : ℤ) : ℝ≥0∞ :=
  if j ≤ i ∧ |((ell - k : ℤ) : ℝ)| ≤ 5 * ((i : ℝ) - (j : ℝ) + 1) then
    ENNReal.ofReal (Real.exp (-c₀ * positionOverlapDelay i j)) else 0

/- Each starting cell has its mass times the source exponential tail on an output cell. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
