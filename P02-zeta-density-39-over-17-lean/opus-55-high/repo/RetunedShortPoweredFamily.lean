module
public import RetunedShortTaylorCover
public import MathCollab.Density.Stronger.ShortPoweredHeight
public import MathCollab.Density.Stronger.ShortPoweredFamily
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Real Complex Filter
open scoped Topology ComplexConjugate
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger
open MathCollab.Density

/-- This bound is fixed by sigma and delta, before T and any zero. -/
def smoothPowerBound (a δ : ℝ) : ℕ := ⌈2*a/δ⌉₊

export MathCollab.Density.Stronger (smoothPoweredFamilyScale)

/-- The complete finite powered family, restricted by scale conditions that
are independent of the zero. The original smooth scale remains in q.1.1. -/
def smoothPoweredIndices (a δ T : ℝ) : Finset ((ℤ × ℕ × ℕ) × ℕ × ℕ) :=
  ((smoothTaylorIndices a T).product
    ((Finset.Icc 1 (smoothPowerBound a δ)).product (Finset.range (smoothPowerBound a δ)))).filter
    (fun q => q.2.2 < q.2.1 ∧
      T^(a) ≤ (smoothHalfScale q.1.1 q.1.2.1 : ℝ)^q.2.1 ∧
      (smoothHalfScale q.1.1 q.1.2.1 : ℝ)^q.2.1 ≤ T^(smoothingExponent a))

def smoothPoweredFamilyCoefficient (η a δ T : ℝ) (q : (ℤ × ℕ × ℕ) × ℕ × ℕ) (n : ℕ) : ℂ :=
  normalizedSmoothPoweredCoefficient η T (detectorX δ T) (detectorY a T)
    q.1.1 q.1.2.1 q.1.2.2 q.2.1 n

theorem mem_smoothPoweredIndices {a δ T : ℝ} {q : (ℤ × ℕ × ℕ) × ℕ × ℕ} :
    q ∈ smoothPoweredIndices a δ T ↔
      q.1 ∈ smoothTaylorIndices a T ∧
      1 ≤ q.2.1 ∧ q.2.1 ≤ smoothPowerBound a δ ∧ q.2.2 < q.2.1 ∧
      T^(a) ≤ (smoothHalfScale q.1.1 q.1.2.1 : ℝ)^q.2.1 ∧
      (smoothHalfScale q.1.1 q.1.2.1 : ℝ)^q.2.1 ≤ T^(smoothingExponent a) := by pm_4458

theorem smoothTaylorIndices_card_eventually {σ a : ℝ} (hw : QuadraticWindow σ a) :
    ∀ᶠ T : ℝ in atTop, ((smoothTaylorIndices a T).card : ℝ) ≤ 144*(Real.log T)^2 := by pm_2760 smoothingExponent_pos smoothingExponent_lt_one

/-- At most a fixed multiple of log(T)^2 members, before zeros are selected. -/
theorem smoothPoweredIndices_card_eventually {σ a : ℝ} (hw : QuadraticWindow σ a) (δ : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      ((smoothPoweredIndices a δ T).card : ℝ) ≤
        144*(smoothPowerBound a δ : ℝ)^2*(Real.log T)^2 := by pm_2761

/-- Every member of the fixed family has the required powered scales and
globally bounded normalized coefficients. Threshold precedes every index. -/
theorem smoothPoweredFamily_admissible {σ a η : ℝ}
    (hw : QuadraticWindow σ a) (hη : 0 < η) (δ : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ q ∈ smoothPoweredIndices a δ T,
      T^(a) ≤ (smoothPoweredFamilyScale q : ℝ) ∧
      (smoothPoweredFamilyScale q : ℝ) ≤ (2 : ℝ)^(smoothPowerBound a δ)*T^(smoothingExponent a) ∧
      (smoothPoweredFamilyScale q : ℝ) ≤ T ∧
      ∀ n : ℕ, ‖smoothPoweredFamilyCoefficient η a δ T q n‖ ≤ 1 := by pm_2762 smoothingExponent_lt_one

/-- Complete actual-zero dichotomy: a long smooth detector, or a member of
the finite normalized powered short family at the original ordinate. -/
theorem smooth_long_or_short_powered_cover {σ a δ η : ℝ}
    (hw : QuadraticWindow σ a) (hsigma : 7/9 ≤ σ) (hδ : 0 < δ) (hδ' : δ ≤ 1/8) (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T → riemannZeta ρ = 0 →
      (∃ j ∈ smoothScaleIndices (detectorY a T*(Real.log T)^2),
        T^(smoothingExponent a/2) < (2 : ℝ)^j ∧
        (1/(24*Real.log T) : ℝ) ≤ ‖smoothDetectorBlock ρ (detectorX δ T) (detectorY a T) j‖) ∨
      (∃ q ∈ smoothPoweredIndices a δ T,
        (smoothPoweredFamilyScale q : ℝ)^σ*T^(-2*η) ≤
          ‖detectingPolynomial (smoothPoweredFamilyScale q) (smoothPoweredFamilyCoefficient η a δ T q) ρ.im‖) := by
  pm_2755
  filter_upwards [smooth_long_or_short_Taylor_cover hw hsigma hδ.le hδ',
    short_scale_bounded_power ha hδ,
    exists_normalizedSmoothPowered_height hη (smoothPowerBound a δ)] with T hcover hpower hheight
  pm_2763

end Montgomery.RationalMoment.RightDetector
