module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaMorseChangeVariables

@[expose] public section

/-!
# The original cutoff in the actual quadratic-coordinate amplitude

The weight is the original Poisson cutoff composed with the actual
inverse, multiplied by its Jacobian. Its value at zero keeps that
cutoff; no slope-chart cutoff or uncut amplitude is substituted.
-/

noncomputable section

open Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025


def modelPhaseMorseAmplitude (χ F : ℝ → ℝ) (v z : ℝ) : ℝ :=
  χ (modelPhaseMorseInverse F v z)*deriv (modelPhaseMorseInverse F v) z

theorem modelPhaseMorseAmplitude_contDiffAt
    {χ F : ℝ → ℝ} {σ δ v z : ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) :
    ContDiffAt ℝ ∞ (modelPhaseMorseAmplitude χ F v) z := by
  have hi := modelPhaseMorseInverse_contDiffAt hσ hδ hF hv hz
  exact (hχ.contDiffAt.comp z hi).mul (hi.derivWithin (by simp))

theorem modelPhaseMorseAmplitude_zero
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    modelPhaseMorseAmplitude χ F v 0 =
      χ (modelPhaseInverseSlope F v)*modelPhaseStationaryAmplitude F v := by
  rw [modelPhaseMorseAmplitude,modelPhaseMorseInverse_zero hσ hδ hF hv,
    (modelPhaseMorseInverse_hasDerivAt_zero hσ hδ hF hv).deriv]


