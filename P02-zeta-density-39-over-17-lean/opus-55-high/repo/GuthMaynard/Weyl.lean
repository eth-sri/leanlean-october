module
public import GuthMaynard.SecondOrderMeanValue
public import GuthMaynard.NativeSource.GuthMaynard.Weyl

@[expose] public section

open Complex Finset Set
open scoped InnerProductSpace

namespace RiemannZeta.GuthMaynard

/-!
# Weyl differencing for the logarithmic phase

The correlation phase below is the phase produced by one A-process shift.
Its curvature is controlled on a dyadic interval and is fed into the
multi-period B-process from `SecondDerivative.lean`.
-/

export GuthMaynard.NativeMoment (padded_logarithmic_correlation_eq logarithmicDifferenceCurvature_bounds logarithmicDifference_secondDifference_bounds padded_logarithmic_correlation_norm_le logarithmicDifference_B_process integerLogarithmicSum_eq logarithmicDifferencePhase_secondDifference hasDerivAt_logarithmicDifferencePhase_deriv interval_weyl_differencing_complex padded_logarithmic_correlation_norm_le_of_lt hasDerivAt_logarithmicDifferencePhase logarithmicCorrelationBound logarithmicDifferencePhase norm_integerLogarithmicTerm integerLogarithmicTerm shiftDistance)

end RiemannZeta.GuthMaynard
