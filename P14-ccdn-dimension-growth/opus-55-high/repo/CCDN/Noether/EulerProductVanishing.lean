/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Noether.EulerGenericFactors
import CCDN.ForMathlib.Matrix
import CCDN.Noether.EulerPairSpecialization

/-!
Characteristic-independent vanishing on products. A generic integral
identity is proved in the fraction field and then specialized; this includes
inseparable and repeated factors in every characteristic.

A nonzero Euler kernel vector forces every maximal universal
coefficient minor to vanish after specialization.
-/

namespace CCDN
section
open MvPolynomial Module

theorem eulerClosedForm_minor_eq_zero_of_kernel
    {F : Type*} [Field F] (k : ℕ) (f : Polynomial (Polynomial F))
    (u : EulerPairSpace F k) (hu : u ≠ 0)
    (hker : eulerClosedFormOperator k f u = 0)
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    ((eulerClosedFormCoefficientMatrix k f).submatrix rows cols).det = 0 := by
  by_contra hdet
  let A := eulerClosedFormCoefficientMatrix k f
  have hlo := A.le_rank_of_det_submatrix_ne_zero rows cols hdet
  have hr : A.rank = Fintype.card (EulerColumns k) := by
    apply le_antisymm (Matrix.rank_le_card_width _)
    simpa only [card_eulerColumns] using hlo
  let T := (bivariateCoefficients F).comp (eulerClosedFormOperator k f)
  have hsum : ∑ i, (eulerPairBasis F k).repr u i • A.col i = 0 := by
    have hh := congrArg T ((eulerPairBasis F k).sum_repr u)
    rw [map_sum] at hh
    simp only [map_smul] at hh
    change (∑ i, (eulerPairBasis F k).repr u i • A.col i) =
      bivariateCoefficients F (eulerClosedFormOperator k f u) at hh
    grind
  have hz := Fintype.linearIndependent_iff.mp (by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank,
      ← Matrix.rank_eq_finrank_span_cols, hr]) _ hsum
  apply hu
  apply (eulerPairBasis F k).repr.injective
  ext i
  simpa using hz i

end

section
open Polynomial

variable (k a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = k + 2)
include ha hb hab

theorem genericEulerProduct_minor_eq_zero
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    ((eulerClosedFormCoefficientMatrix k
      (genericEulerFactorLeft a b * genericEulerFactorRight a b)).submatrix rows cols).det = 0 := by
  let R := MvPolynomial (EulerFactorParameters a b) ℤ
  let F := FractionRing R
  let φ := algebraMap R F
  let G := genericEulerFactorLeft a b
  let H := genericEulerFactorRight a b
  have hφ := IsFractionRing.injective R F
  have hmap : Function.Injective (bivariateMap φ) := Polynomial.map_injective _ (Polynomial.map_injective φ hφ)
  have hg :=
    (bivariateTotalDegree_map_le φ G).trans (eulerPolynomialFromCoefficients_degree a _)
  have hh :=
    (bivariateTotalDegree_map_le φ H).trans (eulerPolynomialFromCoefficients_degree b _)
  have hne : eulerFactorPair a b (bivariateMap φ G) (bivariateMap φ H) ≠ 0 := by
    intro hz
    have he := eulerFactorPair_map φ a b G H
    apply genericEulerFactorPair_ne_zero a b ha hb
    apply Prod.ext
    · aesop
    · aesop
  obtain ⟨u, hu, hk⟩ := exists_eulerFactorKernel k a b ha hb hab
    (bivariateMap φ G) (bivariateMap φ H) hg hh hne
  have hz := eulerClosedForm_minor_eq_zero_of_kernel k _ u hu hk rows cols
  apply hφ
  rwa [map_zero, eulerClosedForm_minor_map, map_mul]

/-- Every maximal Euler minor vanishes on a product with two positive
degree budgets, over an arbitrary commutative coefficient ring. -/
theorem eulerClosedForm_minor_eq_zero_of_product
    {R : Type*} [CommRing R]
    (g h : R[X][X]) (hg : bivariateTotalDegree g ≤ a)
    (hh : bivariateTotalDegree h ≤ b)
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    ((eulerClosedFormCoefficientMatrix k (g * h)).submatrix rows cols).det = 0 := by
  let φ := genericEulerFactorSpecialization a b g h
  have hz := congrArg φ (genericEulerProduct_minor_eq_zero k a b ha hb hab rows cols)
  rw [map_zero, eulerClosedForm_minor_map, map_mul,
    genericEulerFactorLeft_specialize a b g h hg,
    genericEulerFactorRight_specialize a b g h hh] at hz
  exact hz

