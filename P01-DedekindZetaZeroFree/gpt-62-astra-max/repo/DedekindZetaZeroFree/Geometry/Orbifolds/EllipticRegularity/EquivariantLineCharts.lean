module

public import DedekindZetaZeroFree.Analysis.QuadraticForms.TestDifferentialFriedrichsLaplacian
public import DedekindZetaZeroFree.Analysis.EllipticRegularity.IntegerSobolevEstimates

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPContLocalOrbifold

open MeasureTheory
open KPContLocalNorm KPContLocalEnergy KPContLocalRegularity

structure LineChart (n : ℕ) where
  stabilizer : Type
  group : Group stabilizer
  finite : Fintype stabilizer
  action : stabilizer →* (Space n ≃ₗᵢ[ℝ] Space n)
  lineAction : stabilizer →* ℂˣ
  unitary : ∀ g, ‖(lineAction g : ℂ)‖ = 1
  inner : LocalBall n
  outer : LocalBall n
  concentric : inner.center = outer.center
  radii_lt : inner.radius < outer.radius
  fixes_center : ∀ g, action g outer.center = outer.center
  densityLower : ℝ
  densityUpper : ℝ
  ellipticityLower : ℝ
  ellipticityUpper : ℝ
  densityLower_pos : 0 < densityLower
  ellipticityLower_pos : 0 < ellipticityLower
  coefficients : Coefficients outer densityLower densityUpper
    ellipticityLower ellipticityUpper
  smooth_coefficients : SmoothNearClosedBall coefficients
  density_invariant : ∀ g, ∀ x ∈ outer.carrier,
    coefficients.density (action g x) = coefficients.density x
  cutoff : Space n → ℝ
  cutoff_smooth : ContDiff ℝ (⊤ : ℕ∞) cutoff
  cutoff_compact : HasCompactSupport cutoff
  cutoff_support : tsupport cutoff ⊆ outer.carrier
  cutoff_one : ∀ x ∈ Metric.closedBall inner.center inner.radius, cutoff x = 1
  cutoff_invariant : ∀ g, ∀ x, cutoff (action g x) = cutoff x

attribute [instance] LineChart.group LineChart.finite

end DedekindZetaZeroFree.KPContLocalOrbifold

end
