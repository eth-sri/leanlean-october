module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import MathCollab.Density.Stronger.Atkinson.ReciprocalSecondDerivativeBounds

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology ContDiff

namespace TaoTrudgianYang2025

export MathCollab.Density.Stronger.Atkinson (iteratedDeriv_two_real_inv)

end TaoTrudgianYang2025
