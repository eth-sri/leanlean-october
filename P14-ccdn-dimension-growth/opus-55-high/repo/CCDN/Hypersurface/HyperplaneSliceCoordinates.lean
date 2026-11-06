/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.PolynomialPredicates
import CCDN.Hypersurface.IntegerHyperplaneSlices
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Coordinate transport between the graph-hyperplane construction and
the finite integral-point count. -/

namespace CCDN
section
open MvPolynomial

section
variable {n : ℕ} (D : ℤ) (a : Fin n → ℤ)

/-- The integer normal vector `(D, -a 0, …, -a (n - 1))` of the hyperplane
`D * x 0 = ∑ a i * x (i + 1)`. -/
def graphIntegerNormal : IntPoint (n + 1) :=
  Fin.cons D (fun i => -a i)

/-- If `|D|` and every `|a i|` are at most `H`, then every coordinate of `graphIntegerNormal D a`
has absolute value at most `H`. -/
lemma graphIntegerNormal_height {H : ℕ}
    (hD : |D| ≤ (H : ℤ)) (ha : ∀ i, |a i| ≤ (H : ℤ)) :
    ∀ i, |(graphIntegerNormal D a i : ℝ)| ≤ (H : ℝ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact_mod_cast hD
  · simpa [graphIntegerNormal, Fin.cons_succ, Int.cast_neg, abs_neg] using
      (show |(a j : ℝ)| ≤ (H : ℝ) by exact_mod_cast ha j)

end

/-- Integral equations suffice for the rational zero-locus map used by
the count: the only coordinate change is deleting coordinate zero. -/
theorem integer_slice_map_of_option_equations {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (D : ℤ) (a : Fin n → ℤ)
    (g : ℤ → MvPolynomial (Fin n) ℤ)
    (hslice : ∀ k (x : Option (Fin n) → ℤ),
      D * x none - ∑ i, a i * x (some i) = k →
      eval x (rename (finSuccEquiv' 0) f) = 0 →
      eval (fun i => x (some i)) (g k) = 0)
    (B : ℝ) (k : ℤ) (x : IntPoint (n + 1))
    (hx : x ∈ integerSlicePoints (zeroLocus (map (Int.castRingHom ℚ) f))
      B (graphIntegerNormal D a) k) :
    rationalPoint (deleteIntegerCoordinate 0 x) ∈
      zeroLocus (map (Int.castRingHom ℚ) (g k)) := by
  let e : Fin (n + 1) ≃ Option (Fin n) := finSuccEquiv' 0
  let z : Option (Fin n) → ℤ := x ∘ e.symm
  have hznone : z none = x 0 := by aesop
  have hzsome (i : Fin n) : z (some i) = deleteIntegerCoordinate 0 x i := by aesop
  have hlevel := (Finset.mem_filter.mp hx).2
  have hfxQ :=
    (mem_integralPoints.mp (Finset.mem_filter.mp hx).1).2
  have hfxZ : eval x f = 0 := by
    have he : ((eval x f : ℤ) : ℚ) =
        eval (rationalPoint x) (map (Int.castRingHom ℚ) f) := by
      exact map_eval (Int.castRingHom ℚ) x f
    exact Int.cast_injective (he.trans hfxQ)
  have hz : eval z (rename e f) = 0 := by
    rw [eval_rename]
    simpa [z, Function.comp_def, Equiv.symm_apply_apply] using hfxZ
  have hgZ := hslice k z (by
    change (∑ i, graphIntegerNormal D a i * x i) = k at hlevel
    rw [Fin.sum_univ_succ] at hlevel
    simp [graphIntegerNormal, Fin.cons_zero, Fin.cons_succ, neg_mul,
      Finset.sum_neg_distrib] at hlevel
    bound) hz
  change eval (rationalPoint (deleteIntegerCoordinate 0 x))
    (map (Int.castRingHom ℚ) (g k)) = 0
  have he : eval (rationalPoint (deleteIntegerCoordinate 0 x))
      (map (Int.castRingHom ℚ) (g k)) =
      ((eval (fun i => z (some i)) (g k) : ℤ) : ℚ) := by
    change eval (fun i => (deleteIntegerCoordinate 0 x i : ℚ))
      (map (Int.castRingHom ℚ) (g k)) = _
    simpa [Function.comp_def, Int.coe_castRingHom, hzsome] using
      (map_eval (Int.castRingHom ℚ) (fun i => z (some i)) (g k)).symm
  rw [he, hgZ, Int.cast_zero]

