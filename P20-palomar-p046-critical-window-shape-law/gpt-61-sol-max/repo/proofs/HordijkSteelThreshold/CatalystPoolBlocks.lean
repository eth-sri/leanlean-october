
import proofs.HordijkSteelThreshold.AmbientIndependence




namespace HordijkSteelThreshold

open RAF.Polymer

/-- A reaction is open relative to a specified prospective internal catalyst
pool.  Unlike ambient openness, this predicate retains the catalyst pool that
must eventually lie in the marked core. -/
def catalystPoolOpen {n : Nat} (ω : AmbientCoord n → Prop)
    (C : Finset _) (r : Reaction n)  :=
  ∃ x ∈ C, ω (x, r)





end HordijkSteelThreshold
