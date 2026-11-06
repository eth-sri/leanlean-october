module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaMorseInverseJetBounds
public import TaoTrudgianYang2025.BetaMorseGlobalIntegral
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Actual transformed-weight derivatives of every order

Even jet coordinates are original cutoff derivatives at the inverse point;
odd coordinates are derivatives of the actual inverse. The finite product
and chain calculus is proved against these functions before use in bounds.
-/

noncomputable section

open Set Expdb Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

theorem iteratedDeriv_modelPhaseMorseWeight_eq
    {χ F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) (n : ℕ) :
    iteratedDeriv n (modelPhaseMorseWeight χ F v) z =
      iteratedDeriv n (modelPhaseMorseAmplitude χ F v) z := by
  apply Filter.EventuallyEq.iteratedDeriv_eq
  pm_5907 x hx modelPhaseMorseWeight_eq

end TaoTrudgianYang2025
