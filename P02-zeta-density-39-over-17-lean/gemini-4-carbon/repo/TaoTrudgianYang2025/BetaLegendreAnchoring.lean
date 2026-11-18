module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaLegendreCompact

@[expose] public section

/-!
# Anchored values of the actual Legendre phase

The original phase may contain an arbitrary additive constant. We remove
that constant by subtracting the dual/reference discrepancy at an anchor.
The value estimate is derived by mean value from the genuine first-derivative
error, uniformly along the entire compact interval.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

def anchoredLegendreError (F : ℝ → ℝ) (σ w v : ℝ) : ℝ :=
  (modelPhaseLegendreDual F v - referenceModelPrimitive σ⁻¹ v) -
    (modelPhaseLegendreDual F w - referenceModelPrimitive σ⁻¹ w)

end TaoTrudgianYang2025
