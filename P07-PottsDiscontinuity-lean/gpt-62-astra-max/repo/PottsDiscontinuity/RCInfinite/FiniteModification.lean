module

public import PottsDiscontinuity.RCInfinite.Cylinders
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.Measure.Trim
public import PottsDiscontinuity.RCInfinite.FiniteEnergy
@[expose] public section

open MeasureTheory Set

namespace PottsDiscontinuity.RCInfinite
open FK
noncomputable section
open scoped Classical

/-- Prescribe exactly the states in a finite edge set. -/
def setEdges (F : Finset Edge) (ξ : Edge → Bool) (ω : LatticeConfiguration) : LatticeConfiguration :=
  fun e => if e ∈ F then ξ e else ω e

end
end PottsDiscontinuity.RCInfinite
