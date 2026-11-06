/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Height.Box
import Mathlib.Algebra.MvPolynomial.PDeriv
import CCDN.Determinant.PlaneSingularities
import CCDN.Determinant.SingularDeterminant
import CCDN.ForMathlib.MvPolynomial
import CCDN.ForMathlib.MvPolynomialDerivative
import CCDN.Hypersurface.NonabsoluteHypersurfaceCount

/-! The singular locus of an irreducible rational hypersurface has a
coefficient-uniform codimension-two integer point bound. A nonzero partial
derivative gives the proper intersection used in the count. -/

namespace CCDN
section
open MvPolynomial

/-- The rational points of the singular locus of the hypersurface `f = 0`: the common zeros of
`f` and all its partial derivatives. -/
def singularHypersurfaceLocus {n : ℕ} (f : MvPolynomial (Fin n) ℚ) :
    Set (RatPoint n) :=
  {x | eval x f = 0 ∧ ∀ j, eval x (pderiv j f) = 0}

variable {n : ℕ} (f : MvPolynomial (Fin (n + 2)) ℚ) (hir : Irreducible f) {B : ℝ}
include hir

theorem singular_hypersurface_count_le
    (hB : 0 ≤ B) :
    (count (singularHypersurfaceLocus f) B : ℝ) ≤
      (n + 2 : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * (2 * B + 1) ^ n := by
  obtain ⟨j, hproper, hdeg⟩ : ∃ j, ¬ f ∣ pderiv j f ∧
      (pderiv j f).totalDegree < f.totalDegree := by
    have hd := MvPolynomial.totalDegree_pos_of_irreducible hir
    obtain ⟨j, hj⟩ := exists_pderiv_ne_zero hd fun n hn _ ↦ Nat.cast_ne_zero.mpr hn.ne'
    have hdeg : (pderiv j f).totalDegree < f.totalDegree := by
      have := pderiv_totalDegree_le f j
      omega
    exact ⟨j, not_dvd_pderiv_of_pderiv_ne_zero hir.ne_zero hj, hdeg⟩
  have hsub : singularHypersurfaceLocus f ⊆ zeroLocus f ∩ zeroLocus (pderiv j f) :=
    fun x hx => ⟨hx.1, hx.2 j⟩
  exact (Nat.cast_le.mpr (count_mono hsub le_rfl)).trans
    (proper_intersection_count_le_box f (pderiv j f) hir.prime hproper le_rfl hdeg.le hB)

/-- The singular locus of an irreducible rational hypersurface in `n + 2` variables has at most
`(3 * (n + 2)) ^ n * deg f ^ 2 * B ^ n` integral points of height at most `B`, for every
`B ≥ 1`. -/
theorem singular_hypersurface_dimension_growth
    (hB : 1 ≤ B) :
    (count (singularHypersurfaceLocus f) B : ℝ) ≤
      (3 * (n + 2) : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * B ^ n := by
  calc
    _ ≤ (n + 2 : ℝ) ^ n * f.totalDegree ^ 2 * (2 * B + 1) ^ n :=
      singular_hypersurface_count_le f hir (by linarith)
    _ ≤ (n + 2 : ℝ) ^ n * f.totalDegree ^ 2 * (3 * B) ^ n := by
      gcongr
      linarith
    _ = _ := by grind [mul_pow]

