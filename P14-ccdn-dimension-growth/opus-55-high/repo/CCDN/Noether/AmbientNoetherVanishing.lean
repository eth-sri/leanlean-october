/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Noether.AmbientNoetherForms
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CCDN.Noether.EulerPairSpecialization
import CCDN.Noether.EulerProductVanishing
import CCDN.Noether.UniversalPlaneBadWitness
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! The constructed ambient coefficient forms vanish on every geometrically
reducible homogeneous equation, in every characteristic. -/

namespace CCDN
section
open MvPolynomial

section
variable {R σ : Type*} [CommRing R]

lemma universalPlanePolynomial_mul
    (g h : MvPolynomial σ R) :
    universalPlanePolynomial (g * h) = universalPlanePolynomial g * universalPlanePolynomial h := by
  simp [universalPlanePolynomial, map_mul]

/-- The universal plane restriction of `f` has bivariate total degree at most the total degree of
`f`. -/
lemma universalPlanePolynomial_totalDegree_le
    (f : MvPolynomial σ R) : bivariateTotalDegree (universalPlanePolynomial f) ≤ f.totalDegree := by
  simpa [universalPlanePolynomial, bivariateTotalDegree, AlgEquiv.symm_apply_apply] using
    universalPlaneMap_planeDegree_le f

/-- If `g` and `h` have total degrees at most `a` and `b`, with `a, b > 0` and `a + b = k + 2`,
then every minor of order `(k + 2)^2 - 1` of the Euler closed-form coefficient matrix of the
universal plane restriction of `g * h` vanishes. -/
theorem ambientEuler_minor_eq_zero_of_product
    (k a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = k + 2)
    (g h : MvPolynomial σ R) (hg : g.totalDegree ≤ a) (hh : h.totalDegree ≤ b)
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    ((eulerClosedFormCoefficientMatrix k (universalPlanePolynomial (g * h))).submatrix
      rows cols).det = 0 := by
  rw [universalPlanePolynomial_mul]
  exact eulerClosedForm_minor_eq_zero_of_product k a b ha hb hab _ _
    ((universalPlanePolynomial_totalDegree_le g).trans hg)
    ((universalPlanePolynomial_totalDegree_le h).trans hh) rows cols

end

/-- Reducibility forces the entire parameter determinant to vanish,
including the zero homogeneous equation. -/
theorem ambientEuler_minor_eq_zero_of_not_irreducible {K σ : Type*} [Field K]
    (k : ℕ) (f : MvPolynomial σ K) (hf : f.IsHomogeneous (k + 2))
    (hred : ¬Irreducible f)
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    ((eulerClosedFormCoefficientMatrix k (universalPlanePolynomial f)).submatrix
      rows cols).det = 0 := by
  by_cases hf0 : f = 0
  · subst f
    simpa using ambientEuler_minor_eq_zero_of_product
      k 1 (k + 1) (by omega) (by omega) (by omega)
      (0 : MvPolynomial σ K) 0 (by simp) (by simp) rows cols
  have hd := hf.totalDegree hf0
  obtain ⟨g, h, hgu, hhu, he⟩ := (irreducible_or_factor (by
    intro hu
    have hh := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega)).resolve_left hred
  have hgh0 := he ▸ hf0
  have hg0 := (mul_ne_zero_iff.mp hgh0).1
  have hh0 := (mul_ne_zero_iff.mp hgh0).2
  have hgpos := totalDegree_pos_of_ne_zero_of_not_isUnit hg0 hgu
  have hhpos := totalDegree_pos_of_ne_zero_of_not_isUnit hh0 hhu
  rw [he]
  exact ambientEuler_minor_eq_zero_of_product k _ _ hgpos hhpos (by
    rwa [he, totalDegree_mul_of_isDomain hg0 hh0] at hd) g h le_rfl le_rfl rows cols

