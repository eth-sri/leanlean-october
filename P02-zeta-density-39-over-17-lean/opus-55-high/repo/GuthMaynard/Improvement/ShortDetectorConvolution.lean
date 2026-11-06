module
/- Adapted actual short coefficients; generic audited arithmetic and phases reused. -/
public import MathCollab.Density.DetectorConvolution
public import GuthMaynard.Improvement.ShortFixedDetectorFamily
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Set Filter
open scoped Topology
noncomputable section
namespace GuthMaynard.Improvement

/-- The actual block coefficients as a finite arithmetic function. -/
def shortDetectorBlockCoefficients (T : ℝ) (N j : ℕ) : ArithmeticFunction ℂ where
  toFun n := if n ∈ Finset.Ioc N (2*N) then shortDetectorTaylorCoefficient T N j n else 0
  map_zero' := by simp

theorem shortDetectorBlockCoefficients_apply (T : ℝ) (N j n : ℕ) :
    shortDetectorBlockCoefficients T N j n =
      if n ∈ Finset.Ioc N (2*N) then shortDetectorTaylorCoefficient T N j n else 0 := rfl

theorem shortDetectorBlockCoefficients_norm_le {T : ℝ} {N : ℕ}
    (hT : 0 < T) (hN : 0 < N) (j n : ℕ) :
    ‖shortDetectorBlockCoefficients T N j n‖ ≤ (n.divisors.card : ℝ) := by
  pm_8708 shortDetectorBlockCoefficients_apply norm_shortDetectorTaylorCoefficient_le

/-- Every nonzero convolution coefficient has the literal product support. -/
theorem shortDetectorBlockCoefficients_pow_support (T : ℝ) (N j k n : ℕ)
    (hn : ((shortDetectorBlockCoefficients T N j)^k) n ≠ 0) :
    0 < n ∧ n ≤ (2*N)^k := by
  induction k generalizing n with
  | zero =>
    simp only [pow_zero, ArithmeticFunction.one_apply] at hn
    split_ifs at hn with he
    grind
    grind
  | succ k ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply] at hn
    obtain ⟨p, hp, hmul⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    have ha : ((shortDetectorBlockCoefficients T N j)^k) p.1 ≠ 0 := left_ne_zero_of_mul hmul
    have hb : shortDetectorBlockCoefficients T N j p.2 ≠ 0 := right_ne_zero_of_mul hmul
    have hmem : p.2 ∈ Finset.Ioc N (2*N) := by
      by_contra h
      exact hb (by simp [shortDetectorBlockCoefficients_apply, h])
    have hi := ih p.1 ha
    pm_4285
    exact Nat.mul_le_mul hi.2 (Finset.mem_Ioc.mp hmem).2

theorem shortDetectorBlockCoefficients_pow_lower {N : ℕ} (hN : 0 < N)
    (T : ℝ) (j k n : ℕ) (hn : ((shortDetectorBlockCoefficients T N j)^(k+1)) n ≠ 0) :
    N^(k+1) < n := by pm_4286 shortDetectorBlockCoefficients_apply shortDetectorBlockCoefficients

section
variable (T : ℝ) (N j k : ℕ) (s : ℂ)
include T N j k s
/-- Finite support, proved for the actual powers, gives absolute convergence. -/
theorem shortDetectorBlockCoefficients_pow_LSeriesSummable :
    LSeriesSummable (fun n => ((shortDetectorBlockCoefficients T N j)^k) n) s := by pm_4287 shortDetectorBlockCoefficients shortDetectorBlockCoefficients_pow_support

/-- The finite L-series of the convolution power is the literal k-th power. -/
theorem shortDetectorBlockCoefficients_LSeries_pow :
    LSeries (fun n => ((shortDetectorBlockCoefficients T N j)^k) n) s =
      (LSeries (shortDetectorBlockCoefficients T N j) s)^k := by pm_4288 shortDetectorBlockCoefficients_pow_LSeriesSummable
end

end GuthMaynard.Improvement
