module
public import GuthMaynard.SecondOrderMeanValue

@[expose] public section

open Complex Finset Set
open scoped BigOperators InnerProductSpace

namespace RiemannZeta.GuthMaynard

/-!
# Weyl differencing for the logarithmic phase

The correlation phase below is the phase produced by one A-process shift.
Its curvature is controlled on a dyadic interval and is fed into the
multi-period B-process from `SecondDerivative.lean`.
-/














/-- Symmetric natural-number distance between two shifts. -/
def shiftDistance (h k : Nat) : Nat := (h - k) + (k - h)



end RiemannZeta.GuthMaynard
