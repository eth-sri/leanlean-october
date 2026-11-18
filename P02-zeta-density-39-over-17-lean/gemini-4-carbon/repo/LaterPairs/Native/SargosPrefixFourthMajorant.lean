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
public import LaterPairs.Native.SargosPrefixMass

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                         

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem norm_sargosFinitePrefix_le_fourierMajorant {N H : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (hH : H ≤ N) :
    ‖sargosFinitePrefix f H‖ ≤ ∑ k : ZMod N, sargosPrefixMajorant k*‖ZMod.dft f k‖ := by
  rw [sargosFinitePrefix_eq_fourier]
  exact (norm_sum_le _ _).trans (by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_sargosPrefixKernel_le_majorant hH k)
        (norm_nonneg _))

end TaoTrudgianYang2025
