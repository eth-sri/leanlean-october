module
public import LaterPairs.PhysicalSmoothDetector
public import RetunedShortTaylorCover
public import RetunedSmoothDetector
public import MathCollab.Density.Stronger.ShortPoweredHeight
public import MathCollab.Density.Stronger.ShortTaylorCover
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Set Filter
open scoped BigOperators Topology ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger
open MathCollab.Density

export Montgomery.RationalMoment.RightDetector (smoothTaylorIndices_card_le_log)

export MathCollab.Density.Stronger (shortTaylor_cutoff_error_eventually)

section
variable {σ a δ : ℝ} (hw : PhysicalDetectorWindow σ a)
include σ a δ hw
/-- The detected short block produces a member of a fixed finite family;
only the selected index depends on rho. -/
theorem smooth_short_Taylor_cover :
    ∀ᶠ T : ℝ in atTop, ∀ (ρ : ℂ) (j : ℤ),
      σ ≤ ρ.re → ρ.re ≤ 1 →
      j ∈ smoothScaleIndices (detectorY a T*(Real.log T)^2) →
      detectorX δ T/2 < (2 : ℝ)^j →
      (2 : ℝ)^j ≤ T^(smoothingExponent a/2) →
      (1/(24*Real.log T) : ℝ) ≤ ‖smoothDetectorBlock ρ (detectorX δ T) (detectorY a T) j‖ →
      ∃ p ∈ smoothTaylorIndices a T, p.1 = j ∧
        detectorX δ T/4 ≤ (smoothHalfScale p.1 p.2.1 : ℝ) ∧
        (smoothHalfScale p.1 p.2.1 : ℝ) ≤ T^(smoothingExponent a/2) ∧
        (smoothHalfScale p.1 p.2.1 : ℝ)^σ/(192*Real.log T) ≤
          ‖smoothTaylorMember a δ T p ρ.im‖ := by pm_4882 smoothingExponent_lt_one_physical

/-- Every actual slab zero lies in the long smooth-block case or is detected
by the fixed short Taylor family, with no moment premise. -/
theorem smooth_long_or_short_Taylor_cover (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/8) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T → riemannZeta ρ = 0 →
      (∃ j ∈ smoothScaleIndices (detectorY a T*(Real.log T)^2),
        T^(smoothingExponent a/2) < (2 : ℝ)^j ∧
        (1/(24*Real.log T) : ℝ) ≤ ‖smoothDetectorBlock ρ (detectorX δ T) (detectorY a T) j‖) ∨
      (∃ p ∈ smoothTaylorIndices a T,
        detectorX δ T/4 ≤ (smoothHalfScale p.1 p.2.1 : ℝ) ∧
        (smoothHalfScale p.1 p.2.1 : ℝ) ≤ T^(smoothingExponent a/2) ∧
        (smoothHalfScale p.1 p.2.1 : ℝ)^σ/(192*Real.log T) ≤
          ‖smoothTaylorMember a δ T p ρ.im‖) := by
  pm_7095 hw
  pm_4478 a
end

end Montgomery.RationalMoment.RightDetector.Physical
