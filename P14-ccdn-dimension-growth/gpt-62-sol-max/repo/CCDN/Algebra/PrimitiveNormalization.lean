/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.PrimitiveIntegerPolynomial
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Primitive models preserve the equation's degree and homogeneous grading,
and integer content removal does not increase coefficient height. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma associated_int_C_mul {σ K : Type*} [Field K] [CharZero K]
    (f : MvPolynomial σ K) {c : ℤ} (hc : c ≠ 0) : Associated f (C (c : K) * f) := by
  rw [mul_comm]
  exact associated_mul_unit_right _ _ ((isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hc)).map C)

/-- Clearing denominators changes the rational polynomial by a unit. -/
theorem exists_integer_model {σ : Type*} (f : MvPolynomial σ ℚ) :
    ∃ g : MvPolynomial σ ℤ, Associated f (map (Int.castRingHom ℚ) g) := by
  obtain ⟨b, g, hb, hg⟩ := mvPolynomial_integer_multiple f
  exact ⟨g, hg.symm ▸ associated_int_C_mul f hb⟩

/-- Removing content preserves the associated rational equation. -/
theorem exists_primitive_integer_model {σ : Type*} (f : MvPolynomial σ ℚ) (hf : f ≠ 0) :
    ∃ g : MvPolynomial σ ℤ, PrimitiveIntegerPolynomial g ∧ Associated f (map (Int.castRingHom ℚ) g) := by
  obtain ⟨u, hu⟩ := exists_integer_model f
  have hu0 : u ≠ 0 := by
    intro hz
    exact hf (hu.eq_zero_iff.mpr (by simp [hz]))
  obtain ⟨c, g, hc, hg, he⟩ := exists_primitive_integer_factor u hu0
  refine ⟨g, hg, hu.trans ?_⟩
  rw [he, map_mul, map_C, Int.coe_castRingHom]
  exact (associated_int_C_mul _ hc).symm

section

variable {σ : Type*} {f : MvPolynomial σ ℚ} {g : MvPolynomial σ ℤ}
  (he : Associated f (map (Int.castRingHom ℚ) g))
include he

lemma rational_model_eq_C_mul : ∃ a : ℚ, IsUnit a ∧ map (Int.castRingHom ℚ) g = C a * f := by
  obtain ⟨u, hu⟩ := he
  obtain ⟨a, ha, ea⟩ := isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  exact ⟨a, ha, by simpa [ea, mul_comm] using hu.symm⟩

/-- Associated rational equations have the same total degree. -/
lemma rational_model_degree (hf : f ≠ 0) : g.totalDegree = f.totalDegree := by
  rw [← totalDegree_map_of_injective (f := Int.castRingHom ℚ) Int.cast_injective g]
  exact le_antisymm (totalDegree_le_of_dvd_of_isDomain he.dvd' hf)
    (totalDegree_le_of_dvd_of_isDomain he.dvd (he.ne_zero_iff.mp hf))

lemma rational_model_homogeneous {d : ℕ} (hf : f.IsHomogeneous d) : g.IsHomogeneous d := by
  obtain ⟨a, ha, h⟩ := rational_model_eq_C_mul he
  exact IsHomogeneous.of_map Int.cast_injective (h.symm ▸ hf.C_mul a)

lemma rational_model_zero_iff (x : σ → ℚ) :
    eval x (map (Int.castRingHom ℚ) g) = 0 ↔ eval x f = 0 := by
  obtain ⟨u, hu⟩ := he
  rw [← hu, eval_mul, mul_eq_zero, or_iff_left]
  exact (u.isUnit.map (eval x)).ne_zero

end
end
end CCDN
