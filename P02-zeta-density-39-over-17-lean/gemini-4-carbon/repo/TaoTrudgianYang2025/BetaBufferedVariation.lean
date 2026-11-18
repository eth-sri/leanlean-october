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
public import TaoTrudgianYang2025.BetaBufferedCutoff
public import TaoTrudgianYang2025.BetaAmplitudeVariation

@[expose] public section

/-!
# Width-independent variation of the actual cutoff-weighted amplitude

The generic two-transition variation theorem is applied to the literal
buffered cutoff. Sampling uses the actual antitone inverse slope.
No plateau hypothesis is imposed on this original source cutoff.
-/

noncomputable section

open Set Expdb

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

theorem modelPhaseBufferedCutoff_eq_band {η : ℝ} (hη : 0 < η) (l r u : ℝ) :
    modelPhaseBufferedCutoff l r η u =
      zetaBandCutoff (l+η) (l+2*η) (r-2*η) (r-η) u := by
  unfold modelPhaseBufferedCutoff zetaBandCutoff
  rw [show l+2*η-(l+η) = η by ring,show r-η-(r-2*η) = η by ring]
  congr 2 <;> field_simp [hη.ne'] <;> ring

end TaoTrudgianYang2025
