module
public import LaterPairs.PhysicalShortTaylorCover
public import RetunedShortPoweredFamily
public import RetunedShortTaylorCover
public import MathCollab.Density.Stronger.ShortPoweredHeight
import WeylPort.Analytic.RealLaplace

public section

open Real Complex Filter
open scoped Topology ComplexConjugate
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger
open MathCollab.Density

/- This bound is fixed by sigma and delta, before T and any zero. -/
/- The complete finite powered family, restricted by scale conditions that
are independent of the zero. The original smooth scale remains in q.1.1. -/

export Montgomery.RationalMoment.RightDetector (mem_smoothPoweredIndices)

section
variable {σ a : ℝ} (hw : PhysicalDetectorWindow σ a)
include σ a hw
theorem smoothTaylorIndices_card_eventually :
    ∀ᶠ T : ℝ in atTop, ((smoothTaylorIndices a T).card : ℝ) ≤ 144*(Real.log T)^2 := by pm_2760 smoothingExponent_pos_physical smoothingExponent_lt_one_physical

/- At most a fixed multiple of log(T)^2 members, before zeros are selected. -/
theorem smoothPoweredIndices_card_eventually (δ : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      ((smoothPoweredIndices a δ T).card : ℝ) ≤
        144*(smoothPowerBound a δ : ℝ)^2*(Real.log T)^2 := by pm_2761
end

/- Every member of the fixed family has the required powered scales and
globally bounded normalized coefficients. Threshold precedes every index. -/
theorem smoothPoweredFamily_admissible {σ a η : ℝ}
    (hw : PhysicalDetectorWindow σ a) (hη : 0 < η) (δ : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ q ∈ smoothPoweredIndices a δ T,
      T^(a) ≤ (smoothPoweredFamilyScale q : ℝ) ∧
      (smoothPoweredFamilyScale q : ℝ) ≤ (2 : ℝ)^(smoothPowerBound a δ)*T^(smoothingExponent a) ∧
      (smoothPoweredFamilyScale q : ℝ) ≤ T ∧
      ∀ n : ℕ, ‖smoothPoweredFamilyCoefficient η a δ T q n‖ ≤ 1 := by pm_2762 smoothingExponent_lt_one_physical

/- Complete actual-zero dichotomy: a long smooth detector, or a member of
the finite normalized powered short family at the original ordinate. -/
theorem smooth_long_or_short_powered_cover {σ a δ η : ℝ}
    (hw : PhysicalDetectorWindow σ a) (hδ : 0 < δ) (hδ' : δ ≤ 1/8) (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T → riemannZeta ρ = 0 →
      (∃ j ∈ smoothScaleIndices (detectorY a T*(Real.log T)^2),
        T^(smoothingExponent a/2) < (2 : ℝ)^j ∧
        (1/(24*Real.log T) : ℝ) ≤ ‖smoothDetectorBlock ρ (detectorX δ T) (detectorY a T) j‖) ∨
      (∃ q ∈ smoothPoweredIndices a δ T,
        (smoothPoweredFamilyScale q : ℝ)^σ*T^(-2*η) ≤
          ‖detectingPolynomial (smoothPoweredFamilyScale q) (smoothPoweredFamilyCoefficient η a δ T q) ρ.im‖) := by
  pm_2755
  pm_6579 hw a
  pm_2763

end Montgomery.RationalMoment.RightDetector.Physical
