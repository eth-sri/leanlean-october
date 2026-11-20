/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import CCDN.Height.Box
public import CCDN.Hilbert.FilteredPrimeDecomposition
public import CCDN.Surface.CurveComponents
public import CCDN.Surface.TopFormAuxiliary
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.ForMathlib.MvPolynomial
import CCDN.Surface.CompleteIntersectionDegreeBudget
import CCDN.Surface.TopFormBadPrimes

/-! The uniform surface auxiliary gives a finite curve cover of
all bounded integer zeros, with total curve degree O(d^(9/2) B^(1/sqrt d)). -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The integral zeros are covered by prime curves of bounded total degree. -/
theorem top_form_surface_curve_components
    (f : MvPolynomial (Fin 3) ℤ) (hir : HasAbsIrreducibleTopForm f) {B : ℝ} (hB : 1 ≤ B) :
    ∃ (S : Finset (Ideal (CoordinatePolynomial 3))) (d : Ideal (CoordinatePolynomial 3) → ℕ),
      (∀ P ∈ S, IsSurfaceCurve (map (Int.castRingHom ℚ) f) P (d P)) ∧
      (∑ P ∈ S, (d P : ℝ)) ≤ topFormAuxiliaryConstant 1 *
        (f.totalDegree : ℝ) ^ (9 / 2 : ℝ) * B ^ (1 / Real.sqrt f.totalDegree) ∧
      ∀ x : IntPoint 3, InBox x B → eval x f = 0 →
        ∃ P ∈ S, rationalPoint x ∈ idealZeroLocus P := by
  classical
  have habs := absolute_irreducible_of_top_homogeneousComponent_irreducible f hir
  have hfQ : Irreducible (map (Int.castRingHom ℚ) f) :=
    rational_irreducible_of_charZero_map f habs
  have hd : 0 < f.totalDegree := absolute_integer_polynomial_totalDegree_pos f habs
  have hdR : (0 : ℝ) < f.totalDegree := by exact_mod_cast hd
  obtain ⟨g, _, hgnd, hgdeg, hgz⟩ := top_form_auxiliary_rational (n := 1) f hir hB
  obtain ⟨S, d, hcomponents, hcover, hbudget⟩ :=
    exists_completeIntersection_curve_components (map (Int.castRingHom ℚ) f)
      (map (Int.castRingHom ℚ) g) hfQ hgnd
  refine ⟨S, d, fun P hP => (hcomponents P hP).toIsSurfaceCurve, ?_, ?_⟩
  · simp only [rational_map_totalDegree] at hbudget
    have hb : (∑ P ∈ S, (d P : ℝ)) ≤ f.totalDegree * (g.totalDegree : ℝ) := by simpa only [Nat.cast_sum] using (show ((∑ P ∈ S, d P : ℕ) : ℝ) ≤ _ by exact_mod_cast hbudget)
    apply hb.trans
    have hc := mul_le_mul_of_nonneg_left hgdeg hdR.le
    norm_num at hc
    rw [Real.sqrt_eq_rpow]
    have he : (f.totalDegree : ℝ) * (f.totalDegree : ℝ) ^ (7 / 2 : ℝ) =
        (f.totalDegree : ℝ) ^ (9 / 2 : ℝ) := by
      conv_lhs => arg 1; rw [← Real.rpow_one (f.totalDegree : ℝ)]
      rw [← Real.rpow_add hdR]
      norm_num
    convert hc using 1
    rw [← he]
    ring_nf
  · intro x hx hxf
    have h : rationalPoint x ∈ zeroLocus (map (Int.castRingHom ℚ) f) ∩
        zeroLocus (map (Int.castRingHom ℚ) g) :=
      ⟨(eval_rationalPoint_map_eq_zero x f).mpr hxf, (eval_rationalPoint_map_eq_zero x g).mpr (hgz x hx hxf)⟩
    simpa only [hcover, Set.mem_iUnion, exists_prop] using h

end
end CCDN
