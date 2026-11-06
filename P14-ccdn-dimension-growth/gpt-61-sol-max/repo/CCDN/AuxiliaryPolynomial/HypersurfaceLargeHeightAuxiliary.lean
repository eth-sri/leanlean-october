/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.AuxiliaryPolynomial.HypersurfaceLargeHeightDegree
public import CCDN.AuxiliaryPolynomial.HypersurfaceNormalizedComparison
public import CCDN.AuxiliaryPolynomial.Nonmultiple
import CCDN.AuxiliaryPolynomial.PolynomialMapAuxiliary

/-! Auxiliary polynomials in the large-height range. The degree is
O_{n,T}(d^(4-1/(n+1))); the leading-coefficient positioning cost is explicit. -/

@[expose] public section
namespace CCDN
open MvPolynomial

private noncomputable def hypersurfaceLargeThreshold (n d : ℕ) (T : ℝ)  :=
  Real.exp (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n) T) *
    ↑d ^ (4 - 1 / (n + 1 : ℝ))

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]


/-- Select a bounded integer degree in the large-height range. The bound is
independent of the box radius and the equation's coefficient height. -/
theorem hypersurface_auxiliary_large_height_degree
     {n d t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : CCDN.IntegerPolynomial (n + 3))
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : CoefficientHeightLE f H)
    (z : Fin t → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (z i) B)
    (T : ℝ) (hT : 0 ≤ T)
    (hheight : 2 * d * (n + 2 : ℝ) * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| +
      T * d * degreeRoot n d) :
    ∃ M : ℕ, ↑M ≤
      (8 * (n + 2 : ℝ) +
          Real.exp (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n) T) + 2) *
        ↑d ^ (4 - 1 / (n + 1 : ℝ)) ∧
      ∃ g : CCDN.IntegerPolynomial (n + 3), g.IsHomogeneous M ∧
        (∀ i, eval (z i) g = 0) ∧ ¬ f ∣ g := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hR : 0 ≤ hypersurfaceLargeThreshold n d T := by unfold hypersurfaceLargeThreshold; positivity
  obtain ⟨M, hMlarge, _, hthreshold, hbound⟩ := auxiliary_integer_degree_selection (8 * d * (n + 2))
    (le_rfl) hR
  have hdPow : ↑d ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) := le_rpow_four_sub_inv hd
  obtain ⟨g, hg⟩ := (show ∃ g, IsPointAuxiliary f g M z from (by
                      let inline_hzB : IsPrimitiveBoxZeroFamily f B z := { one_le_radius := hB, eval_eq_zero := hz, abs_le := hbox, primitive := hprim }
                      classical
                      have hf0 := ne_zero_of_irreducible_map hir
                      have hdM : d ≤ M := by nlinarith
                      by_contra hnone
                      obtain ⟨s, _, hr, hc⟩ := hypersurface_no_auxiliary_normalized_comparison order f hf hd hdM hir
                        H hH hcoeff inline_hzB (dvd_of_not_exists_isPointAuxiliary hnone)
                      have hB := inline_hzB.one_le_radius
                      have hL : 1 ≤ |((order.leadingCoeff f : ℤ) : ℝ)| := by
                        exact_mod_cast Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hf0)
                      have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
                      have hlog := hypersurface_large_height_log_degree_bound  (by omega) hd hMlarge hr
                        B |((order.leadingCoeff f : ℤ) : ℝ)| H (hypersurfaceNormalizedError n) T hB hL hH hT
                        (by simp_all)
                        (by grind)
                        (by simp_all [dimensionRoot, degreeRoot, factorialRoot])
                      have hb := hypersurface_large_degree_bound_of_log_bound hd (lt_of_lt_of_le hd hdM) hlog
                      have hb' := by
                        simpa only [hypersurfaceLargeThreshold, Nat.cast_add, Nat.cast_one] using hb
                      exact (not_lt_of_ge hb') hthreshold))
  refine ⟨M, ?_, g, isPointAuxiliary_iff.mp hg⟩
  unfold hypersurfaceLargeThreshold at hbound
  push_cast at hbound
  nlinarith

end CCDN
