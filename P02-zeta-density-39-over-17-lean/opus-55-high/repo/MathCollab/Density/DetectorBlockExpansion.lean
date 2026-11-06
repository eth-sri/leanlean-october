module
public import MathCollab.Density.DetectorBinomial
public import MathCollab.Density.DetectorDyadic
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

def normalizedDetectorBlock (ρ : ℂ) (T : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2*N), firstDetectorCoefficient T n *
    ((((n : ℝ)/N)^(-ρ.re) : ℝ) : ℂ)*dirichletPhase ((n : ℝ)/N) (-ρ.im)

theorem cpow_neg_eq_real_phase {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    (x : ℂ)^(-ρ) = ((x^(-ρ.re) : ℝ) : ℂ)*dirichletPhase x (-ρ.im) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le,
    Real.rpow_def_of_pos hx, Complex.ofReal_exp, dirichletPhase, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp
  ring

/-- Exact rescaling, including the unit phase of N; no ordinate is shifted. -/
theorem detectorBlock_eq_normalized {N : ℕ} (hN : 0 < N) (ρ : ℂ) (T : ℝ) :
    detectorBlock ρ T N = (N : ℂ)^(-ρ)*normalizedDetectorBlock ρ T N := by pm_4296 detectorBlock normalizedDetectorBlock

theorem norm_normalizedDetectorBlock {N : ℕ} (hN : 0 < N) (ρ : ℂ) (T : ℝ) :
    ‖normalizedDetectorBlock ρ T N‖ = (N : ℝ)^ρ.re*‖detectorBlock ρ T N‖ := by
  pm_6167 detectorBlock_eq_normalized
  pm_4297

/-- Genuine summation and finite-sum interchange for the fixed Taylor family. -/
theorem hasSum_detectorTaylorPolynomial {N : ℕ} (hN : 0 < N) (ρ : ℂ) (T : ℝ) :
    HasSum (fun j : ℕ => (detectorTaylorWeight ρ.re j : ℂ)*detectorTaylorPolynomial T N j ρ.im)
      ((((3/2 : ℝ)^ρ.re : ℝ) : ℂ)*normalizedDetectorBlock ρ T N) := by pm_4298 firstDetectorCoefficient detectorTaylorPolynomial detectorTaylorCoefficient normalizedDetectorBlock

/-- The full Taylor combination is at least the beta-rescaled original block. -/
theorem norm_detectorTaylor_tsum_ge {N : ℕ} (hN : 0 < N) {ρ : ℂ} (hβ : 0 ≤ ρ.re) (T : ℝ) :
    (N : ℝ)^ρ.re*‖detectorBlock ρ T N‖ ≤
      ‖∑' j : ℕ, (detectorTaylorWeight ρ.re j : ℂ)*detectorTaylorPolynomial T N j ρ.im‖ := by
  pm_1458 hasSum_detectorTaylorPolynomial T norm_normalizedDetectorBlock
  pm_4299
  pm_1079 detectorBlock T

end MathCollab.Density
