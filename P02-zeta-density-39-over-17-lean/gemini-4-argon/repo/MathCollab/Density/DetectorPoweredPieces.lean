module
public import MathCollab.Density.DetectorConvolution
public import MathCollab.Density.DetectorPowerScales

@[expose] public section

open Complex Set Filter
open scoped BigOperators Topology ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density


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
    rw [detectingPolynomial, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
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



