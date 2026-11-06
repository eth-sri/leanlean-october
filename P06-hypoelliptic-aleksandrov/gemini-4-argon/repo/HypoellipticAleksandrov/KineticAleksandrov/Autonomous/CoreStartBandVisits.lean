module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumReal
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitMassesStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreStartBandScaling
import Mathlib.Tactic

/-! # Source core-start bound for the same enlarged-strip visit measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal

/- The closed entrance band lies strictly inside the active band. -/
theorem enlargedEntrance_subset_active (c : Clock) : closure c.entrance ⊆ c.active := by
  rw [Clock.entrance, closure_Ioo (by linarith [c.positive])]
  intro v hv
  change c.vbar - 3 * c.r / 4 < v ∧ v < c.vbar + 3 * c.r / 4
  constructor <;> linarith [hv.1, hv.2, c.positive]

/- Cell masses in the source position-visits theorem are the actual starting masses. -/
theorem enlargedVisit_power_sum_eq (nu : Measure Point) [IsFiniteMeasure nu]
    (c : Clock) (s q : ℝ) (hq : 0 < q)
    (hnu : ∀ᵐ p ∂nu, p.velocity 0 ∈ closure c.entrance) :
    (∑' a : ℕ × ℤ, nu (enlargedStartCell c s 0 a.1 a.2) ^ q) =
      ∑' j : ℕ, ∑' k : ℤ, ENNReal.ofReal (enlargedPositionVisitMass nu c s 0 j k ^ q) := by
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro j
  apply tsum_congr
  intro k
  rw [enlargedPositionVisitMass_eq_startCellMass nu c s 0 j k hnu]
  unfold enlargedStartCellMass
  rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq.le,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/- The all-time active mixture of enlarged visits has the source improved band norm. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
