module
public import GuthMaynard.Improvement.UnequalPoissonBridge

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

/-- The actual adaptive smoothing occurring in the unequal two-Poisson reduction. -/
def unequalAdaptive (T δ : ℝ) (K R : ℕ) (f : 𝓢(ℝ, ℝ)) (hT : 0 < T) : 𝓢(ℝ, ℝ) :=
  gmAffineTildeSchwartz
    (gmAffineSecondPoissonCutoff T (T ^ gmAffineIterationEta δ) K R /
      (T ^ gmAffineIterationEta δ))
    (div_pos (gmAffineSecondPoissonCutoff_pos hT (Real.rpow_pos_of_pos hT _))
      (Real.rpow_pos_of_pos hT _)) f

end GuthMaynard.Improvement
