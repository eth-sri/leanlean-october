/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.CharZeroOrGT
public import CCDN.Noether.BivariateTotalDegree
import CCDN.Noether.ClosedFormReducibility

/-!
Scaling the defining equation by a nonzero constant preserves the matrix
rank. This permits monic normalization over fields without enlarging integer
coefficients or clearing extra denominators.

-/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix

variable {R : Type*} [CommRing R] (a : R) {F : Type*} [Field F] (d : ℕ) (f : R[X][X])

/-- Scaling an equation scales the entire matrix. -/
lemma closedFormCoefficientMatrix_smul : closedFormCoefficientMatrix d (a • f) = a • closedFormCoefficientMatrix d f := by
  ext; simp [closedFormEntry_apply,mul_left_comm]

private lemma closedForm_rank_smul (a : F) (ha : a ≠ 0)
    (d : ℕ) (f : F[X][X]) :
    (closedFormCoefficientMatrix d (a • f)).rank = (closedFormCoefficientMatrix d f).rank := by
  rw [closedFormCoefficientMatrix_smul]
  grind [Matrix.rank_smul_of_mem_nonZeroDivisors, mem_nonZeroDivisors_of_ne_zero]

/-- Scalar multiplication of a bivariate polynomial by `a` is multiplication by the constant
polynomial `a`. -/
lemma bivariate_smul_eq_constant_mul :
    a • f = C (C a) * f := by
  aesop

/-- Over a field, multiplying a bivariate polynomial by a nonzero scalar preserves
irreducibility. -/
lemma bivariate_irreducible_smul_iff
    (a : F) (ha : a ≠ 0) (f : F[X][X]) : Irreducible (a • f) ↔ Irreducible f := by
  rw [bivariate_smul_eq_constant_mul]
  exact (associated_unit_mul_left f (C (C a)) (by aesop)).irreducible_iff

/-- Scalar multiplication does not increase the total degree. -/
lemma bivariateTotalDegree_smul_le :
    bivariateTotalDegree (a • f) ≤ bivariateTotalDegree f := by
  unfold bivariateTotalDegree
  simpa using MvPolynomial.totalDegree_smul_le _ _

/-- If the outer leading coefficient of `f` is the nonzero constant `a`, then `a⁻¹ • f` is monic.
Normalizing over the coefficient field means no integer denominators need to be cleared in the
original coefficient matrix. -/
lemma bivariate_monic_normalize
    (a : F) (ha : a ≠ 0) (f : F[X][X]) (hl : f.leadingCoeff = C a) :
    (a⁻¹ • f).Monic := by
  rw [bivariate_smul_eq_constant_mul]
  change (C (C a⁻¹) * f).leadingCoeff = 1
  rw [leadingCoeff_mul, leadingCoeff_C, hl, ← map_mul, inv_mul_cancel₀ ha, map_one]

/-- A reducible `f` of outer degree and total degree `d`, whose outer leading coefficient is a
nonzero constant, has closed-form coefficient matrix of rank at most `2 * d ^ 2 - 2`, in
characteristic zero or greater than `d`. -/
theorem closedForm_rank_drop_of_constant_leading (hd : 0 < d) (hchar : CharZeroOrGT F d)
    (a : F) (ha : a ≠ 0) (f : F[X][X])
    (hl : f.leadingCoeff = C a) (hred : ¬Irreducible f)
    (hdeg : f.natDegree = d) (htotal : bivariateTotalDegree f ≤ d) :
    (closedFormCoefficientMatrix d f).rank + 2 ≤ 2 * d ^ 2 := by
  have hi := fun h =>
    hred ((bivariate_irreducible_smul_iff a⁻¹ (inv_ne_zero ha) f).mp h)
  have hr := closedForm_rank_drop_of_not_irreducible d hd hchar (a⁻¹ • f) (bivariate_monic_normalize a ha f hl) hi
    (by grind [natDegree_smul, inv_ne_zero])
    (by grind [bivariateTotalDegree_smul_le])
  grind [closedForm_rank_smul, inv_ne_zero]

end
end CCDN
