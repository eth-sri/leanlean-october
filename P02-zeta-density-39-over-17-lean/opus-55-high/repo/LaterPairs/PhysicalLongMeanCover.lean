module
public import LaterPairs.PhysicalShortPoweredFamily
public import RetunedLongMeanCover
public import RetunedShortPoweredFamily
public import MathCollab.Density.Stronger.LongMeanCounting
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Real Complex Filter MeasureTheory
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger
open MathCollab.Density

/-- The actual-zero dichotomy with the long alternative expressed as a
critical-line mean. Both alternatives keep the original ordinate. -/
theorem smooth_long_mean_or_short_powered_cover {σ a δ η : ℝ}
    (hw : PhysicalDetectorWindow σ a) (hδ : 0 < δ) (hδ' : δ ≤ 1/8) (hη : 0 < η)
    (A : ℕ) (hA : 3 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T → riemannZeta ρ = 0 →
      ((detectorY a T)^((σ-1/2)/2) ≤
        48*C*Real.sqrt (detectorX δ T)*Real.log T*weightedCriticalMean A ρ.im) ∨
      (∃ q ∈ smoothPoweredIndices a δ T,
        (smoothPoweredFamilyScale q : ℝ)^σ*T^(-2*η) ≤
          ‖detectingPolynomial (smoothPoweredFamilyScale q)
            (smoothPoweredFamilyCoefficient η a δ T q) ρ.im‖) := by
  have hσ := hw.sigma_low
  pm_4338
  filter_upwards [eventually_ge_atTop (2 : ℝ), hm, log_sq_eventually_le_height,
    smooth_long_or_short_powered_cover hw hδ hδ' hη] with T hT hmean hlogSq hcover
  pm_4339
  · apply Or.inl
    pm_4336
    pm_4239
    pm_4337
    pm_4340 a smoothingExponent_lt_one_physical hw
    pm_4238
  · exact Or.inr hshort


end Montgomery.RationalMoment.RightDetector.Physical
