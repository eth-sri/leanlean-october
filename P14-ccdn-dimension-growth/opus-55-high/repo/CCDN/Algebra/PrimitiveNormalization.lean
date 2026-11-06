/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Height.PrimitiveIntegerPolynomial
import Mathlib.Basic.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Primitive models preserve the equation's degree and homogeneous grading,
and integer content removal does not increase coefficient height. -/

namespace CCDN
section
open MvPolynomial

section
variable {σ : Type*} {f g : MvPolynomial σ ℤ} {c : ℤ}

/-- If `f = C c * g` with a nonzero integer `c`, then every coefficient of `g` is at most the
corresponding coefficient of `f` in absolute value. -/
lemma integer_scalar_factor_coefficient_bound
    (hc : c ≠ 0) (he : f = C c * g) (m : σ →₀ ℕ) :
    |(g.coeff m : ℝ)| ≤ |(f.coeff m : ℝ)| := by
  have hc1 : (1 : ℝ) ≤ |(c : ℝ)| := mod_cast Int.one_le_abs hc
  rw [he, coeff_C_mul, Int.cast_mul, abs_mul]
  nlinarith [abs_nonneg (g.coeff m : ℝ)]

end

/-- Every nonzero rational multivariate polynomial has a primitive integer
model differing by a nonzero rational scalar. -/
theorem exists_primitive_integer_model {σ : Type*} (f : MvPolynomial σ ℚ) (hf : f ≠ 0) :
    ∃ (g : MvPolynomial σ ℤ) (a : ℚ), PrimitiveIntegerPolynomial g ∧ a ≠ 0 ∧
      MvPolynomial.map (Int.castRingHom ℚ) g = C a * f := by
  obtain ⟨b, u, hb, hu⟩ := mvPolynomial_integer_multiple f
  obtain ⟨c, g, hc, hg, he⟩ := exists_primitive_integer_factor u (by aesop)
  have hcQ : (c : ℚ) ≠ 0 := mod_cast hc
  refine ⟨g, b / c, hg, div_ne_zero (mod_cast hb) hcQ, ?_⟩
  have hh := congrArg (MvPolynomial.map (Int.castRingHom ℚ)) he
  rw [hu, map_mul, map_C] at hh
  simp at hh
  apply mul_left_cancel₀ (C_eq_zero.not.mpr hcQ)
  rw [← mul_assoc, ← C_mul, mul_div_cancel₀ _ hcQ]
  exact hh.symm

variable {σ : Type*} {f : MvPolynomial σ ℚ} {g : MvPolynomial σ ℤ} {a : ℚ}

/-- An integer polynomial `g` whose image over `ℚ` is a nonzero rational multiple `C a * f` of
a nonzero polynomial `f` has the same total degree as `f`. -/
lemma rational_scalar_model_degree
    (ha : a ≠ 0) (hf : f ≠ 0)
    (he : MvPolynomial.map (Int.castRingHom ℚ) g = C a * f) : g.totalDegree = f.totalDegree := by
  have hd : (MvPolynomial.map (Int.castRingHom ℚ) g).totalDegree = g.totalDegree :=
      totalDegree_map_of_injective Int.cast_injective _
  rw [he, totalDegree_mul_of_isDomain (C_eq_zero.not.mpr ha) hf, totalDegree_C, zero_add] at hd
  exact hd.symm

/-- If the image over `ℚ` of an integer polynomial `g` is `C a * f` for a homogeneous
polynomial `f` of degree `d`, then `g` is homogeneous of degree `d`. -/
lemma rational_scalar_model_homogeneous
    {d : ℕ}
    (he : MvPolynomial.map (Int.castRingHom ℚ) g = C a * f) (hf : f.IsHomogeneous d) :
    g.IsHomogeneous d := by
  apply IsHomogeneous.of_map (f := Int.castRingHom ℚ) Int.cast_injective
  rw [he]
  exact hf.C_mul a

/-- If the image over `ℚ` of an integer polynomial `g` is `C a * f` with `a ≠ 0`, then `g` and
`f` have the same rational zeros. -/
lemma rational_scalar_model_zero_iff
    (ha : a ≠ 0)
    (he : MvPolynomial.map (Int.castRingHom ℚ) g = C a * f) (x : σ → ℚ) :
    eval x (MvPolynomial.map (Int.castRingHom ℚ) g) = 0 ↔ eval x f = 0 := by
  rw [he, eval_mul, eval_C]
  exact mul_eq_zero_iff_left ha

