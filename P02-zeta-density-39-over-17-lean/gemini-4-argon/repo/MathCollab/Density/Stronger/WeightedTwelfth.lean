module
public import MathCollab.Density.Stronger.SeparatedMoment
public import MathCollab.Density.Stronger.WeightedCriticalMean
public import MathCollab.Density.Stronger.CriticalMoment

@[expose] public section

open MeasureTheory Set Filter
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger


theorem zetaMomentCriticalNorm_le_linear (t : ℝ) :
    zetaMomentCriticalNorm t ≤ 4*(1+|t|) := by
  simpa only [zetaMomentCriticalNorm, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    norm_riemannZeta_critical_le_linear t






