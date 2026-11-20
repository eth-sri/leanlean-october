/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.Box
public import Mathlib.Algebra.MvPolynomial.PDeriv
import CCDN.ForMathlib.MvPolynomial
import CCDN.ForMathlib.MvPolynomialDerivative
import CCDN.Hypersurface.NonabsoluteHypersurfaceCount
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! The singular locus of an irreducible rational hypersurface has a
coefficient-uniform codimension-two integer point bound. A nonzero partial
derivative gives the proper intersection used in the count. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The rational points of the singular locus of the hypersurface `f = 0`: the common zeros of
`f` and all its partial derivatives. -/
def singularHypersurfaceLocus {n : ℕ} (f : MvPolynomial (Fin n) ℚ) :
    Set (RatPoint n) :=
  {x | eval x f = 0 ∧ ∀ j, eval x (pderiv j f) = 0}

section

variable {n : ℕ}
  (f : MvPolynomial (Fin (n + 2)) ℚ) (hir : Irreducible f)
  {B : ℝ}
include n f hir B

/-- The singular locus of an irreducible rational hypersurface in `n + 2` variables has at most
`(3 * (n + 2)) ^ n * deg f ^ 2 * B ^ n` integral points of height at most `B`, for every
`B ≥ 1`. -/
theorem singular_hypersurface_dimension_growth (hB : 1 ≤ B) :
    (count (singularHypersurfaceLocus f) B : ℝ) ≤
      (3 * (n + 2) : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * B ^ n := by
  obtain ⟨j, hj⟩ := exists_pderiv_ne_zero (totalDegree_pos_of_irreducible hir)
    (fun _ hn _ => Nat.cast_ne_zero.mpr hn.ne')
  exact proper_intersection_count_le f (pderiv j f) hir.prime (not_dvd_pderiv_of_pderiv_ne_zero hj)
    (pderiv_totalDegree_lt hj).le hB (fun _ _ h => ⟨h.1, h.2 j⟩)

end
end
end CCDN
