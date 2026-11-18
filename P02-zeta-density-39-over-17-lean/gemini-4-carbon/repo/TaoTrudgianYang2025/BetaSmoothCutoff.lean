module
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
public import Mathlib
public import TaoTrudgianYang2025.BetaLegendreAnchoring
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

@[expose] public section

/-!
# Smooth cutoffs on retained real intervals

The plateau and support are constructed from strict endpoint buffers.
Multiplication by the cutoff turns a function smooth near its support
into a globally smooth correction, without extending the original function.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

theorem smoothCutoff_mul_contDiff {χ H : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (hH : ∀ x ∈ tsupport χ, ContDiffAt ℝ ∞ H x) :
    ContDiff ℝ ∞ (fun x => χ x * H x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hH x hx)
  · have he : (fun y => χ y * H y) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [hy, zero_mul, Pi.zero_apply]
    exact contDiffAt_const.congr_of_eventuallyEq he

end TaoTrudgianYang2025
