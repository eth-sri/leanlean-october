/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Hilbert.FilteredPrimeDecomposition
public import CCDN.Surface.CurveComponents
public import CCDN.Surface.TopFormAuxiliary
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.ForMathlib.MvPolynomial
import CCDN.Surface.CompleteIntersectionDegreeBudget
import CCDN.Surface.TopFormBadPrimes

/-! The uniform surface auxiliary gives a finite curve cover of
all bounded integer zeros, with total curve degree O(d^(9/2) B^(1/sqrt d)). -/

public section
namespace CCDN
open MvPolynomial

/-- An absolutely irreducible top form supplies the auxiliary equation, the
rational curve components, and their total degree bound. The curve cover contains every original integer zero in the specified box. -/
theorem top_form_surface_curve_components
    (f : CCDN.IntegerPolynomial 3)
    (hir : HasAbsIrreducibleTopForm f)
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ S : Finset (CCDN.CoordinateIdeal 3),
      ∃ d : CCDN.CoordinateIdeal 3 → ℕ,
        (∀ P ∈ S, IsSurfaceCurve (CCDN.rationalPolynomial f) P (d P) ∧ 0 < d P) ∧
          ((∑ P ∈ S, d P : ℕ) : ℝ) ≤ topFormAuxiliaryConstant 1 *
            ↑f.totalDegree ^ (9 / 2 : ℝ) *
              B ^ (1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ)) ∧
          ∀ x : IntPoint 3, InBox x B → eval x f = 0 →
            ∃ P ∈ S, rationalPoint x ∈ idealZeroLocus P := by
  classical
  have habs := absolute_irreducible_of_top_homogeneousComponent_irreducible f hir
  have hfQ :=
    rational_irreducible_of_charZero_map f habs
  have hd := absolute_integer_polynomial_totalDegree_pos f habs
  have hdR : (0 : ℝ) < f.totalDegree := by exact_mod_cast hd
  obtain ⟨g, hgnd, hgdeg, hgz⟩ := top_form_auxiliary_rational  f hir hB
  have hgdegree : ↑g.totalDegree ≤ topFormAuxiliaryConstant 1 *
      ↑f.totalDegree ^ (7 / 2 : ℝ) *
        B ^ (1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ)) := by
    convert hgdeg using 1; norm_num [degreeRoot]
  obtain ⟨S, d, hcomponents, hcover, hbudget⟩ :=
    exists_completeIntersection_curve_components (CCDN.rationalPolynomial f)
      (CCDN.rationalPolynomial g) hfQ hgnd
  have hmapdegree (p : CCDN.IntegerPolynomial 3) :
      (CCDN.rationalPolynomial p).totalDegree = p.totalDegree :=
      totalDegree_map_of_injective Int.cast_injective _
  have hpower : ↑f.totalDegree * ↑f.totalDegree ^ (7 / 2 : ℝ) =
      (f.totalDegree : ℝ) ^ (9 / 2 : ℝ) := by
    calc
      _ = ↑f.totalDegree ^ 1 * (f.totalDegree : ℝ) ^ (7 / 2 : ℝ) := by
        rw [Real.rpow_one]
      _ = ↑f.totalDegree ^ (1 + 7 / 2) := (Real.rpow_add hdR _ _).symm
      _ = _ := by norm_num
  refine ⟨S, d, fun P hP => ⟨(hcomponents P hP).toIsSurfaceCurve,
    (hcomponents P hP).pos⟩, ?_, ?_⟩
  · have hbudgetR : ((∑ P ∈ S, d P : ℕ) : ℝ) ≤
        ↑f.totalDegree * g.totalDegree := by
      rw [hmapdegree f, hmapdegree g] at hbudget
      exact_mod_cast hbudget
    calc
      _ ≤ (f.totalDegree : ℝ) * g.totalDegree := hbudgetR
      _ ≤ ↑f.totalDegree * (topFormAuxiliaryConstant 1 *
          ↑f.totalDegree ^ (7 / 2 : ℝ) *
            B ^ (1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hgdegree hdR.le
      _ = topFormAuxiliaryConstant 1 *
          (↑f.totalDegree * ↑f.totalDegree ^ (7 / 2 : ℝ)) *
            B ^ (1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [hpower]
  · intro x hx hxf
    have hxsection : rationalPoint x ∈
        zeroLocus (CCDN.rationalPolynomial f) ∩ zeroLocus (CCDN.rationalPolynomial g) :=
      ⟨by simpa [zeroLocus] using hxf, by simpa [zeroLocus] using hgz x hx hxf⟩
    rw [hcover] at hxsection
    simpa only [Set.mem_iUnion, exists_prop] using hxsection

end CCDN
