module
public import MathCollab.Density.DetectorConvolution
public import MathCollab.Density.DetectorPowerScales
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Set Filter
open scoped Topology ComplexConjugate
noncomputable section
namespace MathCollab.Density

/-- Conjugation puts the actual powered coefficients into the positive-phase
convention of `detectingPolynomial`, without changing the zero ordinate. -/
def poweredDetectorCoefficient (T : ℝ) (N j k : ℕ) (n : ℕ) : ℂ :=
  conj (((detectorBlockCoefficients T N j)^k) n)

theorem dirichletPhase_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    dirichletPhase (x/y) t = dirichletPhase x t*dirichletPhase y (-t) := by
  rw [dirichletPhase, dirichletPhase, dirichletPhase, ← Complex.exp_add, Real.log_div hx.ne' hy.ne']
  congr 1
  push_cast
  ring

theorem dirichletPhase_conj (x t : ℝ) :
    conj (dirichletPhase x t) = dirichletPhase x (-t) := by
  rw [dirichletPhase, dirichletPhase, ← Complex.exp_conj]
  congr 1
  simp

theorem norm_detectingPolynomial_conj (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖detectingPolynomial N (fun n => conj (a n)) t‖ =
      ‖detectingPolynomial N a (-t)‖ := by
  rw [← norm_conj (detectingPolynomial N a (-t))]
  congr 1
  simp [detectingPolynomial, map_sum, dirichletPhase_conj]

theorem norm_detectingPolynomial_eq_cpow_sum {N : ℕ} (hN : 0 < N)
    (a : ℕ → ℂ) (t : ℝ) :
    ‖detectingPolynomial N a (-t)‖ =
      ‖∑ n ∈ Finset.Ioc N (2*N), a n*(n : ℂ)^(-(Complex.I*(t : ℂ)))‖ := by
  have he : detectingPolynomial N a (-t) =
      (∑ n ∈ Finset.Ioc N (2*N), a n*(n : ℂ)^(-(Complex.I*(t : ℂ))))*dirichletPhase N t := by
    pm_266 detectingPolynomial Finset.sum_mul Finset.sum_congr n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_trans hN (Finset.mem_Ioc.mp hn).1)
    rw [dirichletPhase_div hnpos (by exact_mod_cast hN), neg_neg]
    have hc := cpow_neg_eq_real_phase hnpos (Complex.I*(t : ℂ))
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, neg_zero, Real.rpow_zero,
      Complex.ofReal_one, one_mul, Complex.mul_im, zero_add] at hc
    rw [Complex.ofReal_natCast] at hc
    rw [hc]
    ring
  rw [he, norm_mul, norm_dirichletPhase, mul_one]

theorem detectorBlockCoefficients_LSeries (T : ℝ) (N j : ℕ) (s : ℂ) :
    LSeries (detectorBlockCoefficients T N j) s =
      ∑ n ∈ Finset.Ioc N (2*N), detectorTaylorCoefficient T N j n*(n : ℂ)^(-s) := by pm_4267 detectorBlockCoefficients detectorBlockCoefficients_apply

theorem norm_detectorTaylorPolynomial_LSeries {N : ℕ} (hN : 0 < N)
    (T t : ℝ) (j : ℕ) :
    ‖detectorTaylorPolynomial T N j t‖ =
      ‖LSeries (detectorBlockCoefficients T N j) (Complex.I*(t : ℂ))‖ := by
  rw [detectorTaylorPolynomial, norm_detectingPolynomial_eq_cpow_sum hN,
    detectorBlockCoefficients_LSeries]

/-- Exact consecutive dyadic partition at any natural base scale. -/
theorem sum_scaled_dyadic_Ioc (f : ℕ → ℂ) (B k : ℕ) :
    (∑ ℓ ∈ Finset.range k, ∑ n ∈ Finset.Ioc (2^ℓ*B) (2*(2^ℓ*B)), f n) =
      ∑ n ∈ Finset.Ioc B (2^k*B), f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rw [show 2^(k+1)*B = 2*(2^k*B) by ring]
    exact Finset.sum_Ioc_consecutive f
      (by nlinarith [show 1 ≤ 2^k by exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))]) (by omega)

theorem detectorBlockCoefficients_pow_LSeries_sum {N k : ℕ} (hN : 0 < N)
    (hk : 0 < k) (T : ℝ) (j : ℕ) (s : ℂ) :
    LSeries (fun n => ((detectorBlockCoefficients T N j)^k) n) s =
      ∑ n ∈ Finset.Ioc (N^k) ((2*N)^k),
        ((detectorBlockCoefficients T N j)^k) n*(n : ℂ)^(-s) := by pm_4268 detectorBlockCoefficients detectorBlockCoefficients_pow_support detectorBlockCoefficients_pow_lower

set_option hygiene false in
macro "pf_54" x1:ident x2:ident x3:ident x4:ident x5:ident x6:ident : tactic => `(tactic| (
  let f := fun n : ℕ => (($x1:ident T N j)^k) n*
    (n : ℂ)^(-(Complex.I*(t : ℂ)))
  have he : ‖$x2:ident T N j t‖^k =
      ‖∑ ℓ ∈ Finset.range k, ∑ n ∈ Finset.Ioc (2^ℓ*N^k) (2*(2^ℓ*N^k)), f n‖ := by
    rw [$x3:ident hN, ← norm_pow,
      ← $x4:ident,
      $x5:ident hN hk, sum_scaled_dyadic_Ioc, mul_pow]
  have hn (ℓ : ℕ) : ‖detectingPolynomial (2^ℓ*N^k) ($x6:ident T N j k) t‖ =
      ‖∑ n ∈ Finset.Ioc (2^ℓ*N^k) (2*(2^ℓ*N^k)), f n‖ := by
    change ‖detectingPolynomial _ (fun n => conj ((($x1:ident T N j)^k) n)) t‖ = _
    rw [norm_detectingPolynomial_conj,
      norm_detectingPolynomial_eq_cpow_sum (by positivity)]
  by_contra h
  push Not at h
  have hs : (∑ ℓ ∈ Finset.range k,
      ‖∑ n ∈ Finset.Ioc (2^ℓ*N^k) (2*(2^ℓ*N^k)), f n‖) <
      ‖$x2:ident T N j t‖^k := by
    calc
      _ < ∑ _ℓ ∈ Finset.range k, ‖$x2:ident T N j t‖^k/(k : ℝ) := by
        apply Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hk⟩
        intro ℓ hℓ
        rw [← hn]
        exact h ℓ hℓ
      _ = _ := by simp; field_simp
  have hb := norm_sum_le (Finset.range k)
    (fun ℓ => ∑ n ∈ Finset.Ioc (2^ℓ*N^k) (2*(2^ℓ*N^k)), f n)
  rw [← he] at hb
  linarith))
/-- A powered component is detected on one of its k fixed dyadic pieces,
with exactly the pigeonhole loss k and at the same ordinate t. -/
theorem exists_poweredDetector_piece {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (T t : ℝ) (j : ℕ) :
    ∃ ℓ ∈ Finset.range k,
      ‖detectorTaylorPolynomial T N j t‖^k/(k : ℝ) ≤
        ‖detectingPolynomial (2^ℓ*N^k) (poweredDetectorCoefficient T N j k) t‖ := by pf_54 detectorBlockCoefficients detectorTaylorPolynomial norm_detectorTaylorPolynomial_LSeries detectorBlockCoefficients_LSeries_pow detectorBlockCoefficients_pow_LSeries_sum poweredDetectorCoefficient

end MathCollab.Density
