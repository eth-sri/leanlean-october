module
public import LaterPairs.PhysicalDetectorParameters
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
theorem detector_eventually_small_physical {σ a δ ε : ℝ}
    (hw : PhysicalDetectorWindow σ a) (hδ : δ ≤ 1/8) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      ‖smoothedDetector ρ (detectorX δ T) (1 / detectorY a T)‖ < ε := by
  pm_4426 a smoothingExponent_pos_physical hw smoothingExponent_lt_one_physical hw.sigma_low.le.trans
  pm_5746 detector_error_scale_physical hw
  pm_4427 a

/-- Uniform detection of every actual zero in the slab, with the exact new
parameters and the same ordinate. This does not yet choose a smooth dyadic block. -/
theorem detectorTail_eventually_large_physical {σ a δ : ℝ}
    (hw : PhysicalDetectorWindow σ a) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/8) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      (1/2 : ℝ) ≤ ‖detectorTail ρ (detectorX δ T) (detectorY a T)‖ := by
  pm_4429 a smoothingExponent_pos_physical hw detector_eventually_small_physical
  have hd := detectorTail_decomposition hX (show 0 < detectorY a T by linarith)
    (show 0 ≤ ρ.re by linarith [hw.sigma_low])
  pm_4428 a


end Montgomery.RationalMoment.RightDetector
