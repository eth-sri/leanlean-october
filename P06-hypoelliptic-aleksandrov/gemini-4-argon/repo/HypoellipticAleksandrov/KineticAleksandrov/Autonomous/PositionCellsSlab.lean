module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCells
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitSumHorizon
import Mathlib.Tactic

/-! # Identifying a truncated time bin with its source start-count slab -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/- The source position-resolved start count on an elapsed half-open time slab. -/
def enlargedPositionSlabMass (nu : Measure Point) (c : Clock) (s x a b : ℝ) (k : ℤ) : ℝ :=
  (nu {p | s + a < p.time ∧ p.time ≤ s + b ∧
    p.position 0 ∈ enlargedPositionCell c.r x k ∧
      p.velocity 0 ∈ closure c.entrance}).toReal

/- A noninitial cell is precisely its slab truncated at the observation horizon. -/
theorem enlargedPositionVisitMass_le_timeVisitMass (nu : Measure Point) [IsFiniteMeasure nu]
    (c : Clock) (s x : ℝ) (j : ℕ) (k : ℤ) :
    enlargedPositionVisitMass nu c s x j k ≤ enlargedTimeVisitMass nu c s j := by
  apply ENNReal.toReal_mono (measure_ne_top nu _)
  apply measure_mono
  intro p hp
  exact ⟨hp.1.1, hp.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
