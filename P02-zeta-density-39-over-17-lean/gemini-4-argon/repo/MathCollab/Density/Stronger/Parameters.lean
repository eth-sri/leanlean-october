module
public import MathCollab.Density.DetectorParameters

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

theorem smoothingExponent_pos {σ : ℝ} (hσ : 3/4 < σ) :
    0 < smoothingExponent σ := by
  have : 0 < σ := by linarith
  unfold smoothingExponent
  positivity

theorem smoothingExponent_lt_one {σ : ℝ} (hσ : 3/4 < σ) :
    smoothingExponent σ < 1 := by
  unfold smoothingExponent
  apply (div_lt_one (by linarith : 0 < 4 * σ)).2
  linarith

theorem smoothingExponent_eq {σ : ℝ} :
    smoothingExponent σ = 3 * lowerExponent σ / 2 := by
  unfold smoothingExponent lowerExponent
  ring



/-- Exact balance of the two short-piece large-value exponents. -/
theorem short_exponent_identities {σ : ℝ} (hσ : 0 < σ) :
    2 * (1 - σ) * smoothingExponent σ = densityExponent σ ∧
      1/2 + (3 - 4 * σ) * lowerExponent σ = densityExponent σ := by
  unfold smoothingExponent lowerExponent densityExponent
  constructor <;> field_simp [hσ.ne'] <;> ring




