module
/- Adapted actual short coefficients; generic audited arithmetic and phases reused. -/
public import MathCollab.Density.DetectorPoweredPieces
public import GuthMaynard.Improvement.ShortDetectorConvolution
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Filter MathCollab.Density
open scoped Topology ComplexConjugate
noncomputable section
namespace GuthMaynard.Improvement

/-- Conjugation puts the actual powered coefficients into the positive-phase
convention of `detectingPolynomial`, without changing the zero ordinate. -/
def shortPoweredDetectorCoefficient (T : ℝ) (N j k : ℕ) (n : ℕ) : ℂ :=
  conj (((shortDetectorBlockCoefficients T N j)^k) n)

theorem shortDetectorBlockCoefficients_LSeries (T : ℝ) (N j : ℕ) (s : ℂ) :
    LSeries (shortDetectorBlockCoefficients T N j) s =
      ∑ n ∈ Finset.Ioc N (2*N), shortDetectorTaylorCoefficient T N j n*(n : ℂ)^(-s) := by pm_4267 shortDetectorBlockCoefficients shortDetectorBlockCoefficients_apply

theorem norm_shortDetectorTaylorPolynomial_LSeries {N : ℕ} (hN : 0 < N)
    (T t : ℝ) (j : ℕ) :
    ‖shortDetectorTaylorPolynomial T N j t‖ =
      ‖LSeries (shortDetectorBlockCoefficients T N j) (Complex.I*(t : ℂ))‖ := by
  rw [shortDetectorTaylorPolynomial, norm_detectingPolynomial_eq_cpow_sum hN,
    shortDetectorBlockCoefficients_LSeries]

section
variable {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
include N k hN hk
theorem shortDetectorBlockCoefficients_pow_LSeries_sum (T : ℝ) (j : ℕ) (s : ℂ) :
    LSeries (fun n => ((shortDetectorBlockCoefficients T N j)^k) n) s =
      ∑ n ∈ Finset.Ioc (N^k) ((2*N)^k),
        ((shortDetectorBlockCoefficients T N j)^k) n*(n : ℂ)^(-s) := by pm_4268 shortDetectorBlockCoefficients shortDetectorBlockCoefficients_pow_support shortDetectorBlockCoefficients_pow_lower

/-- A powered component is detected on one of its k fixed dyadic pieces,
with exactly the pigeonhole loss k and at the same ordinate t. -/
theorem exists_shortPoweredDetector_piece
    (T t : ℝ) (j : ℕ) :
    ∃ ℓ ∈ Finset.range k,
      ‖shortDetectorTaylorPolynomial T N j t‖^k/(k : ℝ) ≤
        ‖detectingPolynomial (2^ℓ*N^k) (shortPoweredDetectorCoefficient T N j k) t‖ := by pf_54 shortDetectorBlockCoefficients shortDetectorTaylorPolynomial norm_shortDetectorTaylorPolynomial_LSeries shortDetectorBlockCoefficients_LSeries_pow shortDetectorBlockCoefficients_pow_LSeries_sum shortPoweredDetectorCoefficient
end

end GuthMaynard.Improvement
