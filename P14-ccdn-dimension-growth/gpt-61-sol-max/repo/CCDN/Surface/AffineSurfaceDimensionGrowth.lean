/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Height.Box
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Surface.AffineSurfaceCountLargeDegree
import CCDN.Surface.PrimitiveSurfaceFixedDegree
import CCDN.Surface.TopFormBadPrimes

/-!
The affine surface bound in every degree at least five. The finitely many
degrees below the large-degree threshold are absorbed in one constant.

Removing integer content from the fixed-degree surface estimate.
The resulting constant is uniform in all integer coefficients.
-/

public section
namespace CCDN
open MvPolynomial

/-- Every fixed degree at least five has a coefficient-uniform linear
integer-point bound when the highest homogeneous part is absolutely
irreducible. The equation need not be primitive. -/
private theorem top_form_surface_fixed_degree_linear_bound (d : ℕ) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : CCDN.IntegerPolynomial 3,
      HasAbsIrreducibleTopForm f →
      f.totalDegree = d → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (CCDN.rationalPolynomial f)) B : ℝ) ≤ C * B := by
  obtain ⟨C, hC, hbound⟩ := primitive_surface_fixed_degree_linear_bound d hd
  refine ⟨C, hC, ?_⟩
  intro f hir hfd B hB
  have hf0 : f ≠ 0 := by aesop
  obtain ⟨c, u, hc, hprim, he⟩ := exists_primitive_integer_factor f hf0
  obtain ⟨hudeg, hutop⟩ := absolute_top_irreducible_of_integer_scalar_factor hc he hir
  have hzero : zeroLocus (CCDN.rationalPolynomial f) =
      zeroLocus (CCDN.rationalPolynomial u) := by
    simp_all [CCDN.zeroLocus, CCDN.rationalPolynomial]
  rw [hzero]
  exact hbound u hprim hutop (hudeg.trans hfd) B hB

end CCDN

namespace CCDN
open MvPolynomial

/-- The fixed-degree surface bounds for the degrees `5 ≤ d < t` hold with one constant. -/
private theorem top_form_surface_bounded_degree_linear_bound (t : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : CCDN.IntegerPolynomial 3,
      HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree → f.totalDegree < t → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (CCDN.rationalPolynomial f)) B : ℝ) ≤ C * B := by
  induction t with
  | zero => exact ⟨1, one_pos, fun _ _ _ ht => absurd ht (Nat.not_lt_zero _)⟩
  | succ t ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    by_cases ht : 5 ≤ t
    · obtain ⟨C', hC', hbound'⟩ := top_form_surface_fixed_degree_linear_bound t ht
      refine ⟨C + C', by positivity, fun f hir hd hlt B hB => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
      · exact (hbound f hir hd hlt B hB).trans (by gcongr; linarith)
      · exact (hbound' f hir heq B hB).trans (by gcongr; linarith)
    · grind

/-- Corrected CCDN Proposition 4.3.4 in every degree at least five: the surface bound
`C d^18 B` for integer equations in three variables with absolutely irreducible top-degree
form. -/
theorem affine_surface_dimension_growth :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : CCDN.IntegerPolynomial 3,
      HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (CCDN.rationalPolynomial f)) B : ℝ) ≤
        C * ↑f.totalDegree ^ 18 * B := by
  obtain ⟨Cbig, hCbig, hbig⟩ := affine_surface_count_large_degree
  obtain ⟨Csmall, hCsmall, hsmall⟩ :=
    top_form_surface_bounded_degree_linear_bound topFormSurfaceThreshold
  refine ⟨Cbig + Csmall, by positivity, fun f hir hd B hB => ?_⟩
  have hdpow : 1 ≤ (f.totalDegree : ℝ) ^ 18 :=
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ f.totalDegree by omega))
  by_cases hlarge : topFormSurfaceThreshold ≤ f.totalDegree
  · exact (hbig f hir hlarge B hB).trans (by gcongr; linarith)
  · calc
      _ ≤ Csmall * B := hsmall f hir hd (by omega) B hB
      _ ≤ (Cbig + Csmall) * 1 * B := by gcongr; linarith
      _ ≤ (Cbig + Csmall) * ↑f.totalDegree ^ 18 * B := by gcongr

end CCDN
