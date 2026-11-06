module
/- Adapted from audited Density proofs; reused scalar Taylor weights unchanged. -/
public import MathCollab.Density.DetectorBlockExpansion
public import GuthMaynard.Improvement.ShortDetectorTaylorFamily
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Filter MathCollab.Density
open scoped Topology
noncomputable section
namespace GuthMaynard.Improvement

def normalizedShortDetectorBlock (ρ : ℂ) (T : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2*N), shortDetectorCoefficient T n *
    ((((n : ℝ)/N)^(-ρ.re) : ℝ) : ℂ)*dirichletPhase ((n : ℝ)/N) (-ρ.im)

section
variable {N : ℕ} (hN : 0 < N) (ρ : ℂ) (T : ℝ)
include N hN ρ T
/-- Exact rescaling, including the unit phase of N; no ordinate is shifted. -/
theorem shortDetectorBlock_eq_normalized :
    shortDetectorBlock ρ T N = (N : ℂ)^(-ρ)*normalizedShortDetectorBlock ρ T N := by pm_4296 shortDetectorBlock normalizedShortDetectorBlock

theorem norm_normalizedShortDetectorBlock :
    ‖normalizedShortDetectorBlock ρ T N‖ = (N : ℝ)^ρ.re*‖shortDetectorBlock ρ T N‖ := by
  pm_6167 shortDetectorBlock_eq_normalized
  pm_4297

/-- Genuine summation and finite-sum interchange for the fixed Taylor family. -/
theorem hasSum_shortDetectorTaylorPolynomial :
    HasSum (fun j : ℕ => (detectorTaylorWeight ρ.re j : ℂ)*shortDetectorTaylorPolynomial T N j ρ.im)
      ((((3/2 : ℝ)^ρ.re : ℝ) : ℂ)*normalizedShortDetectorBlock ρ T N) := by pm_4298 shortDetectorCoefficient shortDetectorTaylorPolynomial shortDetectorTaylorCoefficient normalizedShortDetectorBlock
end

/-- The full Taylor combination is at least the beta-rescaled original block. -/
theorem norm_shortDetectorTaylor_tsum_ge {N : ℕ} (hN : 0 < N) {ρ : ℂ} (hβ : 0 ≤ ρ.re) (T : ℝ) :
    (N : ℝ)^ρ.re*‖shortDetectorBlock ρ T N‖ ≤
      ‖∑' j : ℕ, (detectorTaylorWeight ρ.re j : ℂ)*shortDetectorTaylorPolynomial T N j ρ.im‖ := by
  pm_1458 hasSum_shortDetectorTaylorPolynomial T norm_normalizedShortDetectorBlock
  pm_4299
  pm_1079 shortDetectorBlock T

end GuthMaynard.Improvement
