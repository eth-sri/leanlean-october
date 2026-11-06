module

public import proofs.HordijkSteelThreshold.AmbientIndependence

@[expose] public section

namespace HordijkSteelThreshold

open Filter Topology MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete

/-- A reaction is open relative to a specified prospective internal catalyst
pool.  Unlike ambient openness, this predicate retains the catalyst pool that
must eventually lie in the marked core. -/
def catalystPoolOpen {n : Nat} (ω : AmbientCoord n → Prop)
    (C : Finset (Molecule n)) (r : Reaction n) : Prop :=
  ∃ x ∈ C, ω (x, r)





end HordijkSteelThreshold
