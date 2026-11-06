module
/- Adapted from audited Density proofs; reused scalar Taylor weights unchanged. -/
public import GuthMaynard.Improvement.ShortDetectorDyadic
public import MathCollab.Density.Stronger.GenericTaylorFamily
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Filter MathCollab.Density
open scoped Topology
noncomputable section
namespace GuthMaynard.Improvement

/-- The fixed coefficients in the packet's Taylor family. Neither coordinate
of a zero occurs in this definition. -/
def shortDetectorTaylorCoefficient (T : ℝ) (N j n : ℕ) : ℂ :=
  shortDetectorCoefficient T n * (((2*(n : ℝ)/N-3 : ℝ) : ℂ)^j)

def shortDetectorTaylorPolynomial (T : ℝ) (N j : ℕ) (t : ℝ) : ℂ :=
  detectingPolynomial N (shortDetectorTaylorCoefficient T N j) (-t)

theorem norm_shortDetectorTaylorCoefficient_le {T : ℝ} {N n : ℕ}
    (hT : 0 < T) (hN : 0 < N) (hn : n ∈ Finset.Ioc N (2*N)) (j : ℕ) :
    ‖shortDetectorTaylorCoefficient T N j n‖ ≤ (n.divisors.card : ℝ) := by pm_4329 shortDetectorTaylorCoefficient shortDetectorCoefficient_norm_le

/-- Uniform in the Taylor index and ordinate, before any beta approximation. -/
theorem norm_shortDetectorTaylorPolynomial_le {T : ℝ} {N : ℕ}
    (hT : 0 < T) (hN : 0 < N) (j : ℕ) (t : ℝ) :
    ‖shortDetectorTaylorPolynomial T N j t‖ ≤ 2*(N : ℝ)^2 := by pm_4330 shortDetectorTaylorPolynomial shortDetectorTaylorCoefficient T norm_shortDetectorTaylorCoefficient_le hT

/-- The tail of the actual fixed polynomial family has geometric decay.
Identifying its full weighted series with the beta-dependent block is separate. -/
theorem norm_shortDetectorTaylor_tail_le {T β : ℝ} {N : ℕ}
    (hT : 0 < T) (hN : 0 < N) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (J : ℕ) (t : ℝ) :
    ‖∑' j : ℕ, (detectorTaylorWeight β (j+J) : ℂ)*shortDetectorTaylorPolynomial T N (j+J) t‖ ≤
      3*(N : ℝ)^2*(1/3 : ℝ)^J := by pm_4425 shortDetectorTaylorPolynomial T norm_shortDetectorTaylorPolynomial_le hT

end GuthMaynard.Improvement
