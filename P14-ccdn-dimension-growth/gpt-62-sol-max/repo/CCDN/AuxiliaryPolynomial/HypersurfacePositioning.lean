/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.CharZeroOrGT
public import CCDN.AuxiliaryPolynomial.HypersurfaceAffineCoordinates
public import CCDN.ForMathlib.Matrix
public import CCDN.Noether.GenericPlaneIrreducibility
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CCDN.AuxiliaryPolynomial.HypersurfaceFullOuterDegree
import CCDN.AuxiliaryPolynomial.HypersurfaceGoodDirection
import CCDN.Determinant.GenericPlaneMinor
import CCDN.Determinant.HypersurfaceSmoothPoint

/-! Full-degree monic positioning of an irreducible hypersurface at a
smooth point, using an invertible affine change and a nonzero scalar. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Normalize the leading scalar of the explicit affine coordinate change. -/
def normalizedHypersurfaceCoordinates {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K) :
    MvPolynomial (Option σ) K :=
  C (eval b (homogeneousComponent f.totalDegree f))⁻¹ * hypersurfaceAffineCoordinates a b hb f

section

variable {K σ : Type*} [Field K]
  (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K)
include K σ a b hb f

/-- If the leading form of `f` does not vanish at the direction `b`, then the normalized affine
coordinate change of `f` is monic as a polynomial in the distinguished variable `none`. -/
lemma normalizedHypersurfaceCoordinates_monic
    (hdir : eval b (homogeneousComponent f.totalDegree f) ≠ 0) :
    (optionEquivLeft K σ (normalizedHypersurfaceCoordinates a b hb f)).Monic := by
  unfold normalizedHypersurfaceCoordinates
  rw [map_mul, optionEquivLeft_C]
  apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [Polynomial.leadingCoeff, hypersurfaceAffineCoordinates_full_outer_degree a b hb f hdir,
    hypersurfaceAffineCoordinates_top_coefficient, ← map_mul, inv_mul_cancel₀ hdir, map_one]

lemma normalizedHypersurfaceCoordinates_natDegree
    (hdir : eval b (homogeneousComponent f.totalDegree f) ≠ 0) :
    (optionEquivLeft K σ (normalizedHypersurfaceCoordinates a b hb f)).natDegree = f.totalDegree := by
  rw [normalizedHypersurfaceCoordinates, map_mul, optionEquivLeft_C,
    Polynomial.natDegree_C_mul_of_isUnit ((isUnit_iff_ne_zero.mpr (inv_ne_zero hdir)).map C)]
  exact hypersurfaceAffineCoordinates_full_outer_degree a b hb f hdir

lemma normalizedHypersurfaceCoordinates_totalDegree_le :
    (normalizedHypersurfaceCoordinates a b hb f).totalDegree ≤ f.totalDegree :=
  (totalDegree_mul _ _).trans (by simpa using hypersurfaceAffineCoordinates_totalDegree_le a b hb f)

end

/-- Position the hypersurface at a smooth point with a direction in which its leading form
and its first derivative are both nonzero. The generic plane then has a nonzero slope minor. -/
theorem exists_positioned_genericPlane_minor {K σ : Type*} [Field K] [IsAlgClosed K] [Fintype σ]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f) (hpos : 0 < f.totalDegree)
    (hchar : CharZeroOrGT K (2 * f.totalDegree ^ 2)) :
    ∃ (a b : Option σ → K) (hb : b none ≠ 0),
      (closedFormCoefficientMatrix f.totalDegree
        (genericPlanePolynomial (normalizedHypersurfaceCoordinates a b hb f))).HasNonzeroMinor
          (2 * f.totalDegree ^ 2 - 1) := by
  obtain ⟨a, j, ha, hj⟩ := exists_smooth_hypersurface_point_of_degree_lt_char f hf hpos
    (hchar.mono (by nlinarith))
  obtain ⟨b, hb, hdir, ht⟩ :=
    exists_good_hypersurface_direction_with_coordinate f hf.ne_zero a j hj none
  refine ⟨a, b, hb, exists_genericPlane_minor f.totalDegree hpos _ ?_
    (normalizedHypersurfaceCoordinates_monic a b hb f hdir) ?_ ?_ hchar ?_ ?_⟩
  · exact (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr (inv_ne_zero hdir)).map C)).mpr
      ((MulEquiv.irreducible_iff (hypersurfaceAffineCoordinates a b hb)).mpr hf)
  · exact normalizedHypersurfaceCoordinates_natDegree a b hb f hdir
  · exact normalizedHypersurfaceCoordinates_totalDegree_le a b hb f
  · rw [normalizedHypersurfaceCoordinates, map_mul, hypersurfaceAffineCoordinates_eval_zero, ha, mul_zero]
  · rw [normalizedHypersurfaceCoordinates, pderiv_C_mul, map_mul, eval_C,
      hypersurfaceAffineCoordinates_partial_zero]
    positivity

end
end CCDN
