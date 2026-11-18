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
public import LaterPairs.Native.SargosPrefixFourthMajorant

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                                      

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_sum_Icc_eq_range {A : Type*} [AddCommMonoid A] (a b : ℤ) (f : ℤ → A) :
    (∑ y ∈ Finset.Icc a b, f y) = ∑ j ∈ Finset.range (b+1-a).toNat, f (a+j) := by
  rw [Int.Icc_eq_finset_map,Finset.sum_map]
  rfl

end TaoTrudgianYang2025
