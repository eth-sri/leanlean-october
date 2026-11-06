module
public import RetunedInitialDetector
public import MathCollab.Density.Stronger.SmoothDetector
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Real Complex MeasureTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger

/-- All-zero smooth dyadic detection for the stronger parameters, with no
Weyl or moment premise. The finite list is chosen before rho varies. -/
theorem smoothDetector_eventually_large {σ a δ : ℝ}
    (hw : QuadraticWindow σ a) (hsigma : 7/9 ≤ σ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/8) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      ∃ j ∈ smoothScaleIndices (detectorY a T*(Real.log T)^2),
        detectorX δ T/2 < (2 : ℝ)^j ∧
        (1/(24*Real.log T) : ℝ) ≤
          ‖smoothDetectorBlock ρ (detectorX δ T) (detectorY a T) j‖ := by
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 16,
    log_sq_eventually_le_height, detectorTail_eventually_large hw hsigma hδ hδ']
    with T hT hlog hlogSq hdetect
  pm_4424 a hw


end Montgomery.RationalMoment.RightDetector
