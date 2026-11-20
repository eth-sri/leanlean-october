/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Height.PrimitiveIntegerPolynomial
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Primitive models preserve the equation's degree and homogeneous grading,
and integer content removal does not increase coefficient height. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

section

variable {σ : Type*} {f g : MvPolynomial σ ℤ} {c : ℤ} (hf : f ≠ 0)

include hf in
private lemma integer_scalar_factor_ne_zero (he : f = C c * g) : g ≠ 0 := by
  grind

include hf in
/-- If a nonzero integer polynomial factors as `f = C c * g` with `c ≠ 0`, then `g` has the
same total degree as `f`. -/
lemma integer_scalar_factor_degree (hc : c ≠ 0) (he : f = C c * g) : g.totalDegree = f.totalDegree := by
  rw [he, totalDegree_mul_of_isDomain (C_eq_zero.not.mpr hc) (integer_scalar_factor_ne_zero hf he), totalDegree_C, zero_add]

end

variable {σ : Type*} {f : MvPolynomial σ ℚ} {g : MvPolynomial σ ℤ} {a : ℚ} (ha : a ≠ 0)
    (hf : f ≠ 0) {d : ℕ} (he : rationalEquation g = C a * f)

/-- Every nonzero rational multivariate polynomial has a primitive integer
model differing by a nonzero rational scalar. -/
theorem exists_primitive_integer_model (f : MvPolynomial σ ℚ) (hf : f ≠ 0) :
    ∃ (g : MvPolynomial σ ℤ) (a : ℚ), PrimitiveIntegerPolynomial g ∧ a ≠ 0 ∧
      rationalEquation g = C a * f := by
  obtain ⟨b, u, hb, hu⟩ := mvPolynomial_integer_multiple f
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hu0 : u ≠ 0 := by
    aesop
  obtain ⟨c, g, hc, hg, he⟩ := exists_primitive_integer_factor u hu0
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  refine ⟨g, b / c, hg, div_ne_zero hbQ hcQ, ?_⟩
  have hh := congrArg rationalEquation he
  rw [hu, map_mul, map_C] at hh
  apply mul_left_cancel₀ (C_eq_zero.not.mpr hcQ)
  rw [← mul_assoc, ← C_mul, mul_div_cancel₀ _ hcQ]
  exact hh.symm

include ha hf he in
/-- An integer polynomial `g` whose image over `ℚ` is a nonzero rational multiple `C a * f` of
a nonzero polynomial `f` has the same total degree as `f`. -/
lemma rational_scalar_model_degree : g.totalDegree = f.totalDegree := by
  have hd : (rationalEquation g).totalDegree = g.totalDegree :=
      totalDegree_map_of_injective Int.cast_injective _
  rw [he, totalDegree_mul_of_isDomain (C_eq_zero.not.mpr ha) hf, totalDegree_C, zero_add] at hd
  exact hd.symm

include he in
/-- If the image over `ℚ` of an integer polynomial `g` is `C a * f` for a homogeneous
polynomial `f` of degree `d`, then `g` is homogeneous of degree `d`. -/
lemma rational_scalar_model_homogeneous (hf : f.IsHomogeneous d) :
    g.IsHomogeneous d := by
  apply IsHomogeneous.of_map (f := Int.castRingHom ℚ) Int.cast_injective
  grind [hf.C_mul]

include ha he in
/-- If the image over `ℚ` of an integer polynomial `g` is `C a * f` with `a ≠ 0`, then `g` and
`f` have the same rational zeros. -/
lemma rational_scalar_model_zero_iff (x : σ → ℚ) :
    eval x (rationalEquation g) = 0 ↔ eval x f = 0 := by
  simp_all

/-- A primitive integral representative of an irreducible rational polynomial, differing by a unit. -/
lemma primitive_model_irreducible
    (hir : Irreducible f) :
    ∃ (g : MvPolynomial σ ℤ) (a : ℚ), PrimitiveIntegerPolynomial g ∧ a ≠ 0 ∧
      rationalEquation g = C a * f ∧ Irreducible (rationalEquation g) := by
  obtain ⟨g, a, hg, ha, he⟩ := exists_primitive_integer_model f hir.ne_zero
  refine ⟨g, a, hg, ha, he, he ▸ ?_⟩
  simp_all [irreducible_isUnit_mul]


end
end CCDN
