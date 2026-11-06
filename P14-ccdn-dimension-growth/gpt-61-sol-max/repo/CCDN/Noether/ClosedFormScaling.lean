/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Algebra.CharZeroOrGT
public import CCDN.Noether.BivariateTotalDegree
import CCDN.Noether.ClosedFormGradient
import CCDN.Noether.ClosedFormReducibility

/-!
Scaling the defining equation by a nonzero constant preserves the matrix
rank. This permits monic normalization over fields without enlarging integer
coefficients or clearing extra denominators.

The closed-form coefficient matrix has corank at most one for a monic
irreducible equation of outer degree d whose coefficients have degree at most
D, in characteristic zero or larger than 2dD. This supplies the rank input to
effective Bertini.
-/

public section
namespace CCDN
open Polynomial Matrix Submodule

private lemma bivariateGridPolynomial_natDegree_lt {R : Type*} [CommRing R] {d : ℕ}
    (hd : 0 < d) (v : BivariateGrid d → R) :
    (bivariateGridPolynomial R d v).natDegree < d := by
  by_cases h : bivariateGridPolynomial R d v = 0
  · simp_all
  · exact (natDegree_lt_iff_degree_lt h).mpr (bivariateGridPolynomial_degree_lt v)

private lemma bivariateGridPolynomial_coefficient_natDegree_le {R : Type*} [CommRing R] {d : ℕ}
    (v : BivariateGrid d → R) (i : ℕ) :
    ((bivariateGridPolynomial R d v).coeff i).natDegree ≤ d := by
  apply natDegree_le_of_degree_le
  apply le_of_lt
  rw [degree_lt_iff_coeff_zero]
  intro j hj
  exact bivariateGridPolynomial_coeff_zero d v i j (Or.inr hj)

variable {F : Type*} [Field F] [IsAlgClosed F] (d : ℕ) (f : F[X][X]) (hf : Irreducible f) (hm : f.Monic) (hdeg : f.degree = d) (D : ℕ) (htotal : bivariateTotalDegree f ≤ D) (hchar : CharZeroOrGT F (2 * d * D))

include hf hm hdeg htotal hchar in
/-- For a normalized irreducible equation the entire coefficient kernel
maps into the one-dimensional span of the gradient. -/
private theorem closedForm_kernel_image_le_gradient
     :
    LinearMap.range ((closedFormPair F d).domRestrict
      (closedFormCoefficientMatrix d f).mulVecLin.ker) ≤
      F ∙ (f.derivative, (bivariateCoefficientDerivative F) f) := by
  rintro u ⟨v, rfl⟩
  have hv := (closedFormCoefficientMatrix_kernel d f v.val).mp (LinearMap.mem_ker.mp v.property)
  let p := (closedFormPair F d v.val).1
  let q := (closedFormPair F d v.val).2
  have hfd := natDegree_eq_of_degree_eq_some hdeg
  have hd := hfd ▸ hm.natDegree_pos.mpr hf.ne_one
  have hdD := hfd ▸ (bivariate_natDegree_le_totalDegree f).trans htotal
  have hp : p.natDegree < f.natDegree := hfd ▸ bivariateGridPolynomial_natDegree_lt hd _
  have hq : q.natDegree < f.natDegree := hfd ▸ bivariateGridPolynomial_natDegree_lt hd _
  have hfD (i : ℕ) : (f.coeff i).natDegree ≤ D :=
    (bivariate_coefficient_natDegree_le_totalDegree f i).trans htotal
  have hpD (i : ℕ) : (p.coeff i).natDegree ≤ D :=
    (bivariateGridPolynomial_coefficient_natDegree_le _ i).trans hdD
  have hmchar : CharZeroOrGT F f.natDegree := hchar.mono (by rw [hfd]; nlinarith)
  have hchar' : CharZeroOrGT F ((f.natDegree + (f.natDegree - 1)) * D) :=
    hchar.mono (by rw [hfd]; exact Nat.mul_le_mul_right D (by omega))
  have he : (bivariateCoefficientDerivative F) p * f - p * (bivariateCoefficientDerivative F) f =
      q.derivative * f - q * f.derivative := by
    change (bivariateCoefficientDerivative F) p * f - p * (bivariateCoefficientDerivative F) f -
      q.derivative * f + q * f.derivative = 0 at hv
    linear_combination hv
  obtain ⟨a, ha, hb⟩ := bivariate_closed_form_eq_gradient
    f p q hf hm hp hq D hfD hpD hmchar hchar' he
  apply Submodule.mem_span_singleton.mpr
  refine ⟨a, ?_⟩
  apply Prod.ext
  · aesop
  · aesop

include hf hm hdeg htotal hchar in
/-- No more than one independent coefficient vector solves the closed-form
matrix for an irreducible normalized equation. -/
private theorem closedForm_kernel_finrank_le_one
     :
    Module.finrank F (closedFormCoefficientMatrix d f).mulVecLin.ker ≤ 1 := by
  let U := (closedFormCoefficientMatrix d f).mulVecLin.ker
  let ψ := (closedFormPair F d).domRestrict U
  have hi : Function.Injective ψ := (closedFormPair_injective d).comp Subtype.val_injective
  have he := LinearMap.finrank_range_of_inj hi
  have hl := Submodule.finrank_mono
    (closedForm_kernel_image_le_gradient d f hf hm hdeg D htotal hchar)
  have hs := by
    simpa using finrank_span_le_card (R := F)
      ({(f.derivative, (bivariateCoefficientDerivative F) f)} : Set _)
  exact he ▸ hl.trans hs

include hf hm hdeg htotal hchar in
/-- The matrix on the 2*d² unknown coefficients has rank at least 2*d²-1. -/
theorem closedForm_coefficient_rank_lower
     :
    2 * d ^ 2 ≤ (closedFormCoefficientMatrix d f).rank + 1 := by
  have he := (closedFormCoefficientMatrix d f).mulVecLin.finrank_range_add_finrank_ker
  have hk := closedForm_kernel_finrank_le_one d f hf hm hdeg D htotal hchar
  have hdim : Module.finrank F (ClosedFormColumns d → F) = 2 * d ^ 2 := by
    simp [ClosedFormColumns, BivariateGrid, pow_two, two_mul]
  rw [hdim] at he
  change (closedFormCoefficientMatrix d f).rank + _ = _ at he
  omega

end CCDN

namespace CCDN
open Polynomial Matrix

/-- The closed-form operator is linear in the equation: scaling the equation by `a` scales the
operator by `a`. -/
lemma closedFormOperator_smul_equation {R : Type*} [CommRing R]
    (a : R) (f : R[X][X]) (u : R[X][X] × R[X][X]) :
    closedFormOperator (a • f) u = a • closedFormOperator f u := by
  change _ * (a • f) - _ * (bivariateCoefficientDerivative R) (a • f) -
    _ * (a • f) + _ * (a • f).derivative = a • (_ - _ - _ + _)
  rw [(bivariateCoefficientDerivative R).map_smul, derivative_smul]
  simp only [mul_smul_comm, smul_sub, smul_add]

/-- Scaling the equation by `a` scales its closed-form coefficient matrix by `a`. -/
lemma closedFormCoefficientMatrix_smul {R : Type*} [CommRing R]
    (a : R) (d : ℕ) (f : R[X][X]) :
    closedFormCoefficientMatrix d (a • f) = a • closedFormCoefficientMatrix d f := by
  classical
  ext i j
  change (bivariateCoefficients R (closedFormOperator (a • f)
    (closedFormPair R d (Pi.single j 1)))) i =
    a * (bivariateCoefficients R (closedFormOperator f
      (closedFormPair R d (Pi.single j 1)))) i
  simp_all [closedFormOperator_smul_equation, map_smul]

variable {F : Type*} [Field F]

private lemma closedForm_rank_smul  (a : F) (ha : a ≠ 0)
    (d : ℕ) (f : F[X][X]) :
    (closedFormCoefficientMatrix d (a • f)).rank = (closedFormCoefficientMatrix d f).rank := by
  grind [closedFormCoefficientMatrix_smul, Matrix.rank_smul_of_mem_nonZeroDivisors, mem_nonZeroDivisors_of_ne_zero]

variable {R : Type*} [CommRing R] (a : R) (f : R[X][X])

include R in
/-- Scalar multiplication of a bivariate polynomial by `a` is multiplication by the constant
polynomial `a`. -/
lemma bivariate_smul_eq_constant_mul  :
    a • f = C (C a) * f := by
  aesop

/-- Over a field, multiplying a bivariate polynomial by a nonzero scalar preserves
irreducibility. -/
lemma bivariate_irreducible_smul_iff 
    (a : F) (ha : a ≠ 0) (f : F[X][X]) : Irreducible (a • f) ↔ Irreducible f := by
  rw [bivariate_smul_eq_constant_mul]
  have hu := ((isUnit_iff_ne_zero.mpr ha).map C).map C
  exact (associated_unit_mul_left f (C (C a)) hu).irreducible_iff

include R in
/-- Scalar multiplication does not increase the total degree. -/
lemma bivariateTotalDegree_smul_le  :
    bivariateTotalDegree (a • f) ≤ bivariateTotalDegree f := by
  unfold bivariateTotalDegree
  rw [map_smul]
  exact MvPolynomial.totalDegree_smul_le _ _

/-- If the outer leading coefficient of `f` is the nonzero constant `a`, then `a⁻¹ • f` is monic.
Normalizing over the coefficient field means no integer denominators need to be cleared in the
original coefficient matrix. -/
lemma bivariate_monic_normalize 
    (a : F) (ha : a ≠ 0) (f : F[X][X]) (hl : f.leadingCoeff = C a) :
    (a⁻¹ • f).Monic := by
  rw [bivariate_smul_eq_constant_mul]
  change (C (C a⁻¹) * f).leadingCoeff = 1
  rw [leadingCoeff_mul, leadingCoeff_C, hl, ← map_mul, inv_mul_cancel₀ ha, map_one]

/-- Over an algebraically closed field of characteristic zero, an irreducible `f` of outer degree
`d` whose outer leading coefficient is a nonzero constant has closed-form coefficient matrix of
rank at least `2 * d ^ 2 - 1`; the equation need not be monic. -/
theorem closedForm_rank_lower_of_constant_leading
     [CharZero F] [IsAlgClosed F]
    (d : ℕ) (a : F) (ha : a ≠ 0) (f : F[X][X])
    (hl : f.leadingCoeff = C a) (hf : Irreducible f) (hdeg : f.natDegree = d) :
    2 * d ^ 2 ≤ (closedFormCoefficientMatrix d f).rank + 1 := by
  have hm := bivariate_monic_normalize a ha f hl
  have hi := (bivariate_irreducible_smul_iff a⁻¹ (inv_ne_zero ha) f).mpr hf
  have hd : (a⁻¹ • f).degree = d := by
    rw [degree_eq_natDegree hm.ne_zero, natDegree_smul f (inv_ne_zero ha), hdeg]
  have hr := closedForm_coefficient_rank_lower d _ hi hm hd _ le_rfl (.of_charZero _)
  rwa [closedForm_rank_smul _ (inv_ne_zero ha)] at hr

/-- A reducible `f` of outer degree and total degree `d`, whose outer leading coefficient is a
nonzero constant, has closed-form coefficient matrix of rank at most `2 * d ^ 2 - 2`, in
characteristic zero or greater than `d`. -/
theorem closedForm_rank_drop_of_constant_leading
     (d : ℕ) (hd : 0 < d) (hchar : CharZeroOrGT F d)
    (a : F) (ha : a ≠ 0) (f : F[X][X])
    (hl : f.leadingCoeff = C a) (hred : ¬Irreducible f)
    (hdeg : f.natDegree = d) (htotal : bivariateTotalDegree f ≤ d) :
    (closedFormCoefficientMatrix d f).rank + 2 ≤ 2 * d ^ 2 := by
  have hm := bivariate_monic_normalize a ha f hl
  have hi := fun h =>
    hred ((bivariate_irreducible_smul_iff a⁻¹ (inv_ne_zero ha) f).mp h)
  have hr := closedForm_rank_drop_of_not_irreducible d hd hchar (a⁻¹ • f) hm hi
    ((natDegree_smul f (inv_ne_zero ha)).trans hdeg)
    ((bivariateTotalDegree_smul_le _ _).trans htotal)
  rw [closedForm_rank_smul _ (inv_ne_zero ha)] at hr
  exact hr

end CCDN
