/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.MonomialEvaluationMatrix
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# Elementary determinant bounds

The archimedean Gram determinant estimate is the one used in CCDN §3.3. The row-factor
divisibility lemma isolates a basic arithmetic input to determinant lower bounds; it does not
assert the much stronger local multiplicity estimates of CCDN §2.
-/

@[expose] public section

namespace CCDN

open Matrix

/-- If row `i` is divisible by `d i`, the product of the row factors divides the determinant. -/
theorem prod_row_factors_dvd_det {R : Type*} [CommRing R] {s : ℕ}
    (A : Matrix (Fin s) (Fin s) R)
    (d : Fin s → R) (h : ∀ i j, d i ∣ A i j) : (∏ i, d i) ∣ A.det := by
  classical
  choose Q hQ using h
  have hA : A = Matrix.of (fun i j => d i * Q i j) := by
    ext i j
    exact hQ i j
  rw [hA]
  exact ⟨(Matrix.of Q).det, Matrix.det_mul_column d (Matrix.of Q)⟩

/-- Archimedean Gram determinant bound: if `A` is the real evaluation matrix of `N` monomials of
degree at most `M` at `s` integer points in the box of radius `B ≥ 1`, then `|det (A Aᵀ)| ≤ s! · (N
· B ^ (2 M)) ^ s`. -/
theorem evaluation_gram_det_le {n N s M : ℕ}
    (mon : Fin N → (Fin n →₀ ℕ)) (points : Fin s → (Fin n → ℤ))
    {B : ℝ} (hB : 1 ≤ B) (hpoints : ∀ i, InBox (points i) B)
    (hdeg : ∀ j, (mon j).degree ≤ M) :
    let A := (evaluationMatrix mon points).map ((↑) : ℤ → ℝ)
    |(A * Aᵀ).det| ≤ (s.factorial : ℝ) * ((N : ℝ) * (B ^ M) ^ 2) ^ s := by
  /- Bound the Gram determinant by expanding its determinant and bounding each entry.
  For monomials of degree at most `M` in a radius-`B` box, take `H = B^M`. -/
  intro A
  have hentry (i j : Fin s) : |(A * Aᵀ) i j| ≤ (N : ℝ) * (B ^ M) ^ 2 := by
    calc
      |(A * Aᵀ) i j| = |∑ k, A i k * A j k| := rfl
      _ ≤ ∑ k, |A i k * A j k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin N, (B ^ M) ^ 2 := Finset.sum_le_sum fun k _ => by
        rw [abs_mul, pow_two]
        exact mul_le_mul (abs_monomial_value_le (mon k) (points i) hB (hpoints i) (hdeg k))
          (abs_monomial_value_le (mon k) (points j) hB (hpoints j) (hdeg k))
          (abs_nonneg _) (by positivity)
      _ = _ := by simp
  simpa [nsmul_eq_mul] using Matrix.det_le (abv := AbsoluteValue.abs) hentry

end CCDN
