/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.MonomialEvaluationMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# Elementary determinant bounds

The archimedean Gram determinant estimate is the one used in CCDN §3.3. The row-factor
divisibility lemma isolates a basic arithmetic input to determinant lower bounds; it does not
assert the much stronger local multiplicity estimates of CCDN §2.
-/

namespace CCDN

open Matrix

/-- Bound the Gram determinant by expanding its determinant and bounding each entry.
For monomials of degree at most `M` in a radius-`B` box, take `H = B^M`. -/
theorem abs_gram_det_le {s N : ℕ} (A : Matrix (Fin s) (Fin N) ℝ) {H : ℝ}
    (hH : 0 ≤ H) (hA : ∀ i j, |A i j| ≤ H) :
    |(A * Aᵀ).det| ≤ (s.factorial : ℝ) * ((N : ℝ) * H ^ 2) ^ s := by
  have hentry : ∀ i j, |(A * Aᵀ) i j| ≤ (N : ℝ) * H ^ 2 := by
    intro i j
    calc
      |(A * Aᵀ) i j| = |∑ k, A i k * A j k| := rfl
      _ ≤ ∑ k, |A i k * A j k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin N, H ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul, pow_two]
        exact mul_le_mul (hA i k) (hA j k) (abs_nonneg _) hH
      _ = _ := by simp
  have h := Matrix.det_le (abv := AbsoluteValue.abs) hentry
  simpa using h

