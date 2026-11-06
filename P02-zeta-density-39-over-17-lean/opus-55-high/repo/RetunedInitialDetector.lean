module
public import RetunedDetectorParameters
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Real Complex MeasureTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger
open MathCollab.Density

/-- The actual contour detector is uniformly small for the stronger curve's
parameters. The Weyl input is proved and discharged; no moment is assumed. -/
theorem detector_eventually_small {σ a δ ε : ℝ}
    (hw : QuadraticWindow σ a) (hsigma : 7/9 ≤ σ) (hδ : δ ≤ 1/8) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      ‖smoothedDetector ρ (detectorX δ T) (1 / detectorY a T)‖ < ε := by
  pm_4426 a smoothingExponent_pos hw smoothingExponent_lt_one hw.sigma_low.le.trans
  have hscale := mul_le_mul_of_nonneg_left
    (detector_error_scale (η := 1/96) hw hsigma hδ hT hβ) (show 0 ≤ A*C by positivity)
  pm_4427 a

/-- Uniform detection of every actual zero in the slab, with the exact new
parameters and the same ordinate. This does not yet choose a smooth dyadic block. -/
theorem detectorTail_eventually_large {σ a δ : ℝ}
    (hw : QuadraticWindow σ a) (hsigma : 7/9 ≤ σ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/8) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      (1/2 : ℝ) ≤ ‖detectorTail ρ (detectorX δ T) (detectorY a T)‖ := by
  have hy : ∀ᶠ T : ℝ in atTop, 4 ≤ detectorY a T :=
    (tendsto_rpow_atTop (smoothingExponent_pos hw)).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hy,
    detector_eventually_small hw hsigma hδ' (by norm_num : (0 : ℝ) < 1/4)] with T hT hY hs
  intro ρ hβ hβ' hγ hγ' hzero
  have hX : 1 ≤ detectorX δ T := Real.one_le_rpow hT hδ
  pm_5987 a
  pm_4428 a


end Montgomery.RationalMoment.RightDetector
