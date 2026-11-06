/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module
public import Mathlib

public import PottsDiscontinuity.FK.Model

/-!
# Finite FK events and actual open connectivity

Every configuration has positive mass. Consequently a finite event has zero
probability exactly when it is empty. Connectivity here always uses actual open
graph edges, even if the boundary partition wires the endpoints together.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)



attribute [local instance] configurationMeasurableSpace

section

variable (q : Parameters) (ξ : BoundaryCondition V)


theorem law_support  :
    (law G q ξ).support = Set.univ := by
  ext A
  simp only [Set.mem_univ, iff_true]
  exact (law_pos G q ξ A).ne'

theorem measure_eq_zero_iff 
    (s : Set (Configuration G)) : measure G q ξ s = 0 ↔ s = ∅ := by
  rw [measure, PMF.toMeasure_apply_eq_zero_iff _ MeasurableSpace.measurableSet_top,
    law_support]
  simp

theorem measure_pos_iff 
    (s : Set (Configuration G)) : 0 < measure G q ξ s ↔ s.Nonempty := by
  rw [pos_iff_ne_zero, ne_eq, measure_eq_zero_iff, Set.nonempty_iff_ne_empty]

end

/-- The actual open path event between two original vertices. -/
def connectivityEvent (u v : V)  :=
  {A | ActualConnected G A u v}

end

end PottsDiscontinuity.FK
