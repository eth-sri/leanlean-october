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
public import TaoTrudgianYang2025.BetaSmoothCutoff

@[expose] public section

/-!
# Globally smooth corrections for actual Legendre phases

The correction uses the genuine anchored dual error on the cutoff support.
Its smoothness and all fixed-order uniform bounds are derived from the
original approximate-model hypothesis, not stipulated for an extension.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

theorem anchoredLegendreError_contDiffAt
    {σ δ w v : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hp : 0 < v) :
    ContDiffAt ℝ ∞ (anchoredLegendreError F σ w) v :=
  ((modelPhaseLegendreDual_contDiffAt hσ hδ hF hv).sub
    (referenceModelPrimitive_contDiffAt σ⁻¹ hp)).sub contDiffAt_const

theorem anchoredLegendreError_iteratedDeriv
    {σ δ w v : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hp : 0 < v) (n : ℕ) :
    iteratedDeriv (n+1) (anchoredLegendreError F σ w) v =
      iteratedDeriv (n+1) (modelPhaseLegendreDual F) v -
        iteratedDeriv n (modelPhase σ⁻¹) v := by
  have hN := ENat.natCast_le_of_coe_top_le_withTop le_rfl (n+1)
  have hG := (modelPhaseLegendreDual_contDiffAt hσ hδ hF hv).of_le hN
  have hR := (referenceModelPrimitive_contDiffAt σ⁻¹ hp).of_le hN
  unfold anchoredLegendreError
  rw [iteratedDeriv_fun_sub (hG.sub hR) contDiffAt_const,
    iteratedDeriv_fun_sub hG hR, referenceModelPrimitive_iteratedDeriv σ⁻¹ hp n]
  simp [iteratedDeriv_const]

end TaoTrudgianYang2025
