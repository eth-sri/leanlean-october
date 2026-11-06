/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Statements
import CCDN.Curve.AffineCurveCount
import CCDN.Surface.AuxiliaryExponent

/-! Counting the nonlinear components of a surface section using their
total Hilbert degree and the affine curve counting theorem. -/

public section
namespace CCDN

/-- The curve counting constant is chosen before the finite family and its
degree budget. This is the nonlinear-component part of the corrected surface
estimate for degrees at least sixteen. -/
theorem nonlinear_curve_union_bound :
    ∃ K : ℝ, 0 < K ∧
      ∀ (s : Finset (CCDN.CoordinateIdeal 3))
        (δ : CCDN.CoordinateIdeal 3 → ℕ) (d : ℕ),
      16 ≤ d → ∀ C B : ℝ, 0 ≤ C → 1 ≤ B →
      (∀ P ∈ s, P.IsPrime ∧ 2 ≤ δ P ∧ HasAffineCurveDegree P (δ P)) →
      (∑ P ∈ s, (δ P : ℝ)) ≤ C * ↑d ^ (9 / 2 : ℝ) * B ^ (1 / Real.sqrt d) →
      (count (⋃ P ∈ s, idealZeroLocus P) B : ℝ) ≤
        K * Real.exp 1 * (480 * C + 2 * C ^ 4) * ↑d ^ 18 * B := by
  obtain ⟨K, hK, hcount⟩ := affine_curve_count 3 (by omega)
  refine ⟨K, hK, ?_⟩
  intro s δ d hd C B hC hB hcurve hdegree
  calc
    _ ≤ ∑ P ∈ s, (count (idealZeroLocus P) B : ℝ) := by
      exact_mod_cast count_biUnion_finset_le s idealZeroLocus B
    _ ≤ ∑ P ∈ s, K * curveBound (δ P) B := by
      grind [Finset.sum_le_sum]
    _ = K * ∑ P ∈ s, curveBound (δ P) B := (Finset.mul_sum _ _ _).symm
    _ ≤ K * (Real.exp 1 * (480 * C + 2 * C ^ 4) * ↑d ^ 18 * B) :=
      mul_le_mul_of_nonneg_left
        (sum_curveBound_le_surface_degree_budget s δ hd hC hB (fun P hP => (hcurve P hP).2.1)
          hdegree) hK.le
    _ = _ := by ring

end CCDN
