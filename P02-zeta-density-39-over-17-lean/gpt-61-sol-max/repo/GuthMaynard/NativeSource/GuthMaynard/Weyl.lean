module
public import GuthMaynard.Weyl
public import GuthMaynard.NativeSource.GuthMaynard.SecondOrderMeanValue

@[expose] public section

open Complex Finset Set
open scoped BigOperators InnerProductSpace

namespace GuthMaynard.NativeMoment

-- Share the classical exponential-sum implementation.
export RiemannZeta.GuthMaynard (
  integerLogarithmicSum_eq
  shiftDistance
)

/-!
# Weyl differencing for the logarithmic phase

The correlation phase below is the phase produced by one A-process shift.
Its curvature is controlled on a dyadic interval and is fed into the
multi-period B-process from `SecondDerivative.lean`.
-/

end GuthMaynard.NativeMoment
