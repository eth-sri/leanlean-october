module
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Interval
public import Mathlib.Tactic.Linarith
public import Mathlib.Basic.Real.Basic
public import GuthMaynard.NativeSource.FiniteDirichletPolynomial

@[expose] public section

open Complex Finset

namespace GuthMaynard.NativeMoment

/-- 
The exact interval convention used in Section 13.1 for dyadic Dirichlet polynomials.
`n ∼ N` is interpreted as `n ∈ (N, 2N]`, which matches `Finset.Ioc N (2 * N)`.
-/
def dyadicInterval (N : ℕ) : Finset ℕ :=
  Ioc N (2 * N)

/-- 
An interval-indexed Dirichlet polynomial $D_N(t) = \sum_{n \sim N} a_n n^{-it}$.
-/
noncomputable def dirichletPoly (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ dyadicInterval N, a n * (n : ℂ) ^ (-t * I)

/-- The positive-sign convention used in Guth--Maynard Theorem 1.1. -/
noncomputable def sourceDirichletPoly (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ dyadicInterval N, a n * (n : ℂ) ^ (t * I)

/-- Pointwise complex conjugation of a coefficient sequence. -/
noncomputable def conjugateCoeffs (a : ℕ → ℂ) (n : ℕ) : ℂ := star (a n)

/-- The positive- and negative-sign Dirichlet-polynomial conventions have the
same norms after conjugating the arbitrary coefficient sequence. -/
theorem norm_sourceDirichletPoly_conjugateCoeffs
    (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖sourceDirichletPoly N (conjugateCoeffs a) t‖ = ‖dirichletPoly N a t‖ := by
  have hstar : star (sourceDirichletPoly N (conjugateCoeffs a) t) = dirichletPoly N a t := by
    unfold sourceDirichletPoly conjugateCoeffs dirichletPoly
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [star_mul, star_star,
      mul_comm (star ((n : ℂ) ^ ((t : ℂ) * I))) (a n)]
    congr 1
    have hnPos : 0 < n := by
      rw [dyadicInterval, Finset.mem_Ioc] at hn
      omega
    have hnArg : ((n : ℂ)).arg ≠ Real.pi := by
      change ((((n : ℝ) : ℂ)).arg ≠ Real.pi)
      rw [Complex.arg_ofReal_of_nonneg (by positivity : (0 : ℝ) ≤ n)]
      exact Real.pi_ne_zero.symm
    have hnCast : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
    rw [hnCast]
    have hConj := Complex.cpow_conj (((n : ℝ) : ℂ)) ((t : ℂ) * I) hnArg
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I] at hConj
    convert hConj.symm using 1 <;> simp [neg_mul, mul_neg]
  rw [← hstar, norm_star]

theorem norm_conjugateCoeffs (a : ℕ → ℂ) (n : ℕ) :
    ‖conjugateCoeffs a n‖ = ‖a n‖ := by
  exact norm_star _

/--
Twist coefficients by the unimodular phase produced when the ordinate is
translated by `c`.  The value at `0` is left unchanged; dyadic intervals never
use that index, and this convention makes norm preservation unconditional.
-/
noncomputable def phaseShiftCoeffs (c : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then a n else a n * (n : ℂ) ^ (-c * I)

/-- Translating the ordinate is exactly coefficient phase twisting. -/
theorem dirichletPoly_translate (N : ℕ) (a : ℕ → ℂ) (c t : ℝ) :
    dirichletPoly N a (t + c) = dirichletPoly N (phaseShiftCoeffs c a) t := by
  unfold dirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n := by
    rw [dyadicInterval, Finset.mem_Ioc] at hn
    omega
  have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hnPos.ne'
  rw [phaseShiftCoeffs, ite_eq_right hnPos.ne']
  rw [mul_assoc, ← Complex.cpow_add _ _ hnNe]
  congr 2
  push_cast
  ring

/-- The coefficient twist used for ordinate translation preserves every norm. -/
theorem norm_phaseShiftCoeffs (c : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    ‖phaseShiftCoeffs c a n‖ = ‖a n‖ := by
  by_cases hn : n = 0
  · simp [phaseShiftCoeffs, hn]
  · have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [phaseShiftCoeffs, ite_eq_right hn, norm_mul]
    change ‖a n‖ * ‖((n : ℝ) : ℂ) ^ (-c * I)‖ = ‖a n‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hnPos]
    simp

