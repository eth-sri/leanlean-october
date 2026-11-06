/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

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

variable {K σ : Type*} [Field K] (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K)

include a hb f in
/-- Normalize the leading scalar of the explicit affine coordinate change. -/
def normalizedHypersurfaceCoordinates   :=
  C (eval b (homogeneousComponent f.totalDegree f))⁻¹ * hypersurfaceAffineCoordinates a b hb f

variable (hdir : eval b (homogeneousComponent f.totalDegree f) ≠ 0)

include hdir in
/-- If the leading form of `f` does not vanish at the direction `b`, then the normalized affine
coordinate change of `f` is monic as a polynomial in the distinguished variable `none`. -/
lemma normalizedHypersurfaceCoordinates_monic 
     :
    (optionEquivLeft K σ (normalizedHypersurfaceCoordinates a b hb f)).Monic := by
  unfold normalizedHypersurfaceCoordinates
  rw [map_mul, optionEquivLeft_C]
  apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [Polynomial.leadingCoeff, hypersurfaceAffineCoordinates_full_outer_degree a b hb f hdir,
    hypersurfaceAffineCoordinates_top_coefficient, ← map_mul, inv_mul_cancel₀ hdir, map_one]


/-- The equation `g` is in position for the generic-plane minor: it is irreducible, monic of
degree `d` in the distinguished variable `none`, of total degree at most `d`, and passes through
the origin, where its derivative in the distinguished variable does not vanish. -/
structure IsMonicSmoothAtOrigin {K σ : Type*} [Field K] (g : MvPolynomial (Option σ) K)
    (d : ℕ) : Prop where
  /-- The equation is irreducible. -/
  irreducible : Irreducible g
  /-- The equation is monic in the distinguished variable `none`. -/
  monic : (optionEquivLeft K σ g).Monic
  /-- The equation has degree `d` in the distinguished variable `none`. -/
  natDegree_eq : (optionEquivLeft K σ g).natDegree = d
  /-- The equation has total degree at most `d`. -/
  totalDegree_le : g.totalDegree ≤ d
  /-- The equation vanishes at the origin. -/
  eval_zero : eval 0 g = 0
  /-- The partial derivative in the distinguished variable `none` does not vanish at the
  origin. -/
  pderiv_ne_zero : eval 0 (pderiv none g) ≠ 0

/-- Smooth-point existence and direction avoidance discharge all positioning
hypotheses: the coordinates and the nonzero scalar are actually constructed. -/
theorem exists_monic_smooth_hypersurface_coordinates
    {K σ : Type*} [Field K] [IsAlgClosed K] [Fintype σ]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hpos : 0 < f.totalDegree) (hchar : CharZeroOrGT K f.totalDegree) :
    ∃ (a b : Option σ → K) (hb : b none ≠ 0),
      eval b (homogeneousComponent f.totalDegree f) ≠ 0 ∧
      IsMonicSmoothAtOrigin (normalizedHypersurfaceCoordinates a b hb f) f.totalDegree := by
  obtain ⟨a, j, ha, hj⟩ := exists_smooth_hypersurface_point_of_degree_lt_char f hf hpos hchar
  obtain ⟨b, hb, hdir, ht⟩ :=
    exists_good_hypersurface_direction_with_coordinate f hf.ne_zero a j hj none
  exact ⟨a, b, hb, hdir, (by
                           apply (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr (inv_ne_zero hdir)).map C)).mpr
                           exact (MulEquiv.irreducible_iff (f := hypersurfaceAffineCoordinates a b hb)).mpr hf),
    normalizedHypersurfaceCoordinates_monic a b hb f hdir,
    (by
      unfold normalizedHypersurfaceCoordinates
      rw [map_mul, optionEquivLeft_C,
        Polynomial.natDegree_C_mul_of_isUnit ((isUnit_iff_ne_zero.mpr (inv_ne_zero hdir)).map C)]
      exact hypersurfaceAffineCoordinates_full_outer_degree a b hb f hdir),
    ((totalDegree_mul _ _).trans (by
         simp_all [totalDegree_C, zero_add, hypersurfaceAffineCoordinates_totalDegree_le])),
    (by
      rw [normalizedHypersurfaceCoordinates, map_mul, hypersurfaceAffineCoordinates_eval_zero, ha,
        mul_zero]),
    (by
      rw [normalizedHypersurfaceCoordinates, pderiv_C_mul, map_mul, eval_C,
        hypersurfaceAffineCoordinates_partial_zero]
      exact mul_ne_zero (inv_ne_zero hdir) ht)⟩

/-- Every irreducible positive-degree hypersurface in characteristic zero or larger
than 2*d^2 has an explicitly positioned generic-plane family with a nonzero slope minor. -/
theorem exists_positioned_genericPlane_minor
    {K σ : Type*} [Field K] [IsAlgClosed K] [Fintype σ]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hpos : 0 < f.totalDegree) (hchar : CharZeroOrGT K (2 * f.totalDegree ^ 2)) :
    ∃ (a b : Option σ → K) (hb : b none ≠ 0),
      eval b (homogeneousComponent f.totalDegree f) ≠ 0 ∧
      (closedFormCoefficientMatrix f.totalDegree
        (genericPlanePolynomial (normalizedHypersurfaceCoordinates a b hb f))).HasNonzeroMinor
          (2 * f.totalDegree ^ 2 - 1) := by
  obtain ⟨a, b, hb, hdir, hg⟩ := exists_monic_smooth_hypersurface_coordinates f hf hpos
    (hchar.mono (by nlinarith))
  exact ⟨a, b, hb, hdir, exists_genericPlane_minor f.totalDegree hpos _ hg.irreducible hg.monic
    hg.natDegree_eq hg.totalDegree_le hchar hg.eval_zero hg.pderiv_ne_zero⟩

end
end CCDN
