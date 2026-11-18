module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import MathCollab.Density.Stronger.Atkinson.FiniteWeightVariation
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCutoffVariation
public import MathCollab.Density.Stronger.Atkinson.ZetaBandSecondDerivatives
public import MathCollab.Density.Stronger.Atkinson.AtkinsonFirstDerivative
public import MathCollab.Density.Stronger.Atkinson.FresnelEvaluation
public import MathCollab.Density.Stronger.Atkinson.ContinuousKernelPrimitive
public import MathCollab.Density.Stronger.Atkinson.IntervalSecondDerivativeBounds
public import MathCollab.Density.Stronger.Atkinson.SecondDerivativeComposition
public import MathCollab.Density.Stronger.PointMean.HorizontalEdges
public import MathCollab.Density.Stronger.Fourth.SquareTail
public import LaterPairs.Native.ContinuousThirdDerivative
public import LaterPairs.Native.FiniteSmoothTaylor

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                               

noncomputable section
open Set GafniTao
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem hasDerivAt_iteratedDeriv_finite
    {F : ℝ → ℝ} {x : ℝ} {n j : ℕ} (hj : j < n)
    (hF : ContDiffAt ℝ n F x) :
    HasDerivAt (iteratedDeriv j F) (iteratedDeriv (j+1) F x) x := by
  have hh : ContDiffAt ℝ (1+j) F x := hF.of_le (by
    exact_mod_cast (by omega))
  simpa only [iteratedDeriv_succ] using (contDiffAt_iteratedDeriv_finite (n := 1) (j := j) hh).differentiableAt_one.hasDerivAt

end TaoTrudgianYang2025
