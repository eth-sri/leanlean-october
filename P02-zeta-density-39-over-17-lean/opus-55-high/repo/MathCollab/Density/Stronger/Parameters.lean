module
public import MathCollab.Density.DetectorParameters
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Filter
open scoped Topology

set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Lower powered length exponent in the stronger-curve argument. -/
def lowerExponent (σ : ℝ) : ℝ := 1 / (2 * σ)

/-- Smoothing and upper powered length exponent. -/
def smoothingExponent (σ : ℝ) : ℝ := 3 / (4 * σ)

/-- Full exponent of T, rather than the normalized density coefficient. -/
def densityExponent (σ : ℝ) : ℝ := 3 * (1 - σ) / (2 * σ)

def detectorX (δ T : ℝ) : ℝ := T ^ δ

def detectorY (σ T : ℝ) : ℝ := T ^ smoothingExponent σ

section
variable {σ : ℝ}
include σ
theorem smoothingExponent_pos (hσ : 3/4 < σ) :
    0 < smoothingExponent σ := by
  pm_8944 smoothingExponent

theorem smoothingExponent_lt_one (hσ : 3/4 < σ) :
    smoothingExponent σ < 1 := by
  unfold smoothingExponent
  pm_8023 div_lt_one
  linarith

theorem smoothingExponent_eq :
    smoothingExponent σ = 3 * lowerExponent σ / 2 := by
  unfold smoothingExponent lowerExponent
  ring

theorem densityExponent_pos (hσ : 3/4 < σ) (hσ' : σ < 1) :
    0 < densityExponent σ := by
  pm_8944 densityExponent

/-- The mollifier exponent is chosen before T and all later small losses. -/
theorem exists_detector_exponent (hσ : 3/4 < σ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧
      δ < (1 - smoothingExponent σ) / 12 := by
  refine ⟨min (1/16) ((1 - smoothingExponent σ) / 24), ?_, ?_, ?_⟩
  · exact lt_min (by norm_num) (by have := smoothingExponent_lt_one hσ; positivity)
  · exact (min_le_left _ _).trans_lt (by norm_num)
  · have := smoothingExponent_lt_one hσ
    exact (min_le_right _ _).trans_lt (by linarith)

/-- Exact balance of the two short-piece large-value exponents. -/
theorem short_exponent_identities (hσ : 0 < σ) :
    2 * (1 - σ) * smoothingExponent σ = densityExponent σ ∧
      1/2 + (3 - 4 * σ) * lowerExponent σ = densityExponent σ := by
  unfold smoothingExponent lowerExponent densityExponent
  grind

/-- The long-piece exponent retains a positive saving before mollifier losses. -/
theorem long_exponent_identity (hσ : 0 < σ) :
    2 + (6 - 12 * σ) * smoothingExponent σ / 2 =
      densityExponent σ - (1 - smoothingExponent σ) := by
  unfold smoothingExponent densityExponent
  field_simp [hσ.ne']
  ring
end

theorem long_exponent_saving {σ δ : ℝ}
    (hσ : 3/4 < σ) (hδ : δ < (1 - smoothingExponent σ) / 12) :
    2 + 6 * δ + (6 - 12 * σ) * smoothingExponent σ / 2 <
      densityExponent σ - (1 - smoothingExponent σ) / 2 := by
  have hid := long_exponent_identity (show 0 < σ by linarith)
  linarith

/-- This is the actual scale factor occurring in the proved contour error. -/
theorem detector_error_scale {σ δ T β η : ℝ}
    (hσ : 3/4 < σ) (hδ : δ ≤ 1/8) (hT : 1 ≤ T) (hβ : σ ≤ β) :
    Real.sqrt (detectorX δ T) * (detectorY σ T) ^ (1/2 - β) * T ^ (1/6 + η) ≤
      T ^ (-1/48 + η) := by
  have hTpos : 0 < T := by linarith
  have hproduct : (1/4 : ℝ) ≤ smoothingExponent σ * (β - 1/2) := by
    unfold smoothingExponent
    rw [div_mul_eq_mul_div]
    pm_8023 le_div_iff₀
    nlinarith
  have hsqrt : Real.sqrt (detectorX δ T) = T ^ (δ/2) := by
    rw [detectorX, Real.sqrt_eq_rpow, ← Real.rpow_mul hTpos.le]
    congr 1
    ring
  rw [hsqrt, detectorY, ← Real.rpow_mul hTpos.le,
    ← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
  apply Real.rpow_le_rpow_of_exponent_le hT
  nlinarith

end MathCollab.Density.Stronger
