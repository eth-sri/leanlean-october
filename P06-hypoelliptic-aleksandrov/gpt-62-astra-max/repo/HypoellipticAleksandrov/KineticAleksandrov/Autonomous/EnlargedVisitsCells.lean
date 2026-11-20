module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisits
import Mathlib.Tactic

/-! # Literal time and position cells for enlarged-strip visits

Source: companion paper, Lemma 8.6. The first time bin contains its
left endpoint; all subsequent bins are left-open and right-closed.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- The source time bin, with the initial atom grouped into bin zero. -/
def enlargedTimeBin (r s : ℝ) (j : ℕ) : Set ℝ :=
  if j = 0 then Icc s (s + r ^ 2)
  else Ioc (s + (j : ℝ) * r ^ 2) (s + ((j : ℝ) + 1) * r ^ 2)

/-- A position cell of width `r³`, on a grid with origin `x`. -/
def enlargedPositionCell (r x : ℝ) (k : ℤ) : Set ℝ :=
  Ico (x + (k : ℝ) * r ^ 3) (x + ((k : ℝ) + 1) * r ^ 3)

section
variable (nu : Measure Point) (c : Clock) (s x : ℝ) (j : ℕ) (k : ℤ)
include c

include s x j k in
/-- A full time-position starting cell, with no velocity restriction. -/
def enlargedStartCell : Set Point :=
  {p | p.time ∈ enlargedTimeBin c.r s j ∧
    p.position 0 ∈ enlargedPositionCell c.r x k}

include nu s x j k in
/-- The real starting mass in a time-position cell. -/
def enlargedStartCellMass : ℝ := (nu (enlargedStartCell c s x j k)).toReal

include nu s x j k in
/-- The position-resolved visit mass, retaining the source entrance support explicitly. -/
def enlargedPositionVisitMass : ℝ :=
  (nu (enlargedStartCell c s x j k ∩ {p | p.velocity 0 ∈ closure c.entrance})).toReal

include nu in
/-- The source time count, summed over all positions. -/
def enlargedTimeVisitMass (s : ℝ) (j : ℕ) : ℝ :=
  (nu {p | p.time ∈ enlargedTimeBin c.r s j ∧
    p.velocity 0 ∈ closure c.entrance}).toReal

include s x j k in
/-- The output cell includes precisely the active velocity interval. -/
def enlargedOutputCell : Set Point :=
  enlargedStartCell c s x j k ∩ {p | p.velocity 0 ∈ c.active}

end

/-- Every source time bin is measurable. -/
theorem measurableSet_enlargedTimeBin (r s : ℝ) (j : ℕ) :
    MeasurableSet (enlargedTimeBin r s j) := by
  unfold enlargedTimeBin
  split
  · exact measurableSet_Icc
  · exact measurableSet_Ioc

/-- Every source position cell is measurable. -/
theorem measurableSet_enlargedPositionCell (r x : ℝ) (k : ℤ) :
    MeasurableSet (enlargedPositionCell r x k) := measurableSet_Ico

variable (nu : Measure Point) (c : Clock) (s x : ℝ) (j : ℕ) (k : ℤ)

/-- Starting cells are measurable in the physical spacetime carrier. -/
theorem measurableSet_enlargedStartCell :
    MeasurableSet (enlargedStartCell c s x j k) :=
  ((measurableSet_enlargedTimeBin c.r s j).preimage continuous_time.measurable).inter
    ((measurableSet_enlargedPositionCell c.r x k).preimage
      ((continuous_apply 0).comp continuous_position).measurable)

/-- Output cells are measurable in physical spacetime. -/
theorem measurableSet_enlargedOutputCell :
    MeasurableSet (enlargedOutputCell c s x j k) :=
  (measurableSet_enlargedStartCell c s x j k).inter
    (isOpen_Ioo.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)

/-- Entrance-supported measures have the same cell masses with or without that restriction. -/
theorem enlargedPositionVisitMass_eq_startCellMass
    (hnu : ∀ᵐ p ∂nu, p.velocity 0 ∈ closure c.entrance) :
    enlargedPositionVisitMass nu c s x j k = enlargedStartCellMass nu c s x j k := by
  have heq : nu.restrict {p | p.velocity 0 ∈ closure c.entrance} = nu :=
    Measure.restrict_eq_self_of_ae_mem hnu
  unfold enlargedPositionVisitMass enlargedStartCellMass
  rw [← Measure.restrict_apply (measurableSet_enlargedStartCell c s x j k), heq]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
