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
public import LaterPairs.Native.IntegerIntervalCount
public import LaterPairs.Native.RobertSargosPrimitiveSystem

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                             

noncomputable section
namespace TaoTrudgianYang2025

def robertSargosFrequencyKey (p : RobertSargosPoint) : ℤ × ℤ × ℤ :=
  (p.d,p.q₁,p.q₂)

def robertSargosCoefficientKey (p : RobertSargosPoint) : ℤ × ℤ × ℤ :=
  (p.r,p.h₁,p.h₂)

theorem robertSargos_keys_injective {p q : RobertSargosPoint}
    (hc : robertSargosCoefficientKey p = robertSargosCoefficientKey q)
    (hf : robertSargosFrequencyKey p = robertSargosFrequencyKey q) : p = q := by
  cases p
  cases q
  simp_all [robertSargosCoefficientKey,robertSargosFrequencyKey]

end TaoTrudgianYang2025
