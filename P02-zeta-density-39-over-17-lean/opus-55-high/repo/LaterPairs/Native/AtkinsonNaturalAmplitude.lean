module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

 
                                                                  

                                                              
                                                                      
                                                              


noncomputable section

open Complex Set Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

theorem IntervalC2Bound.comp_div {f : ℝ → ℂ} {a b M R c : ℝ}
    (hf : IntervalC2Bound f a b M R) (hc : 0 < c) :
    IntervalC2Bound (fun y => f (y / c)) (c * a) (c * b) M (R / c) := by pm_2020

end TaoTrudgianYang2025
