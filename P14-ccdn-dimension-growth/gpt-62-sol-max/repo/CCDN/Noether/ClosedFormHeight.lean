/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.BivariateCoefficientMatrix
public import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-! Coefficient and determinant bounds for the integer closed-form matrix. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix

/-- Every coefficient of the integer bivariate polynomial `f` has absolute value at most `H`. -/
def BivariateCoefficientBound (f : ℤ[X][X]) (H : ℝ) : Prop :=
  ∀ i j, |(((f.coeff i).coeff j : ℤ) : ℝ)| ≤ H

/-- Every entry is a shifted coefficient multiplied by the difference of two exponents. -/
private theorem closedFormCoefficientMatrix_entry_bound
    (d : ℕ) (f : ℤ[X][X]) (H : ℝ) (hH : 0 ≤ H)
    (hf : BivariateCoefficientBound f H) (houter : f.natDegree ≤ d)
    (hinner : ∀ i, (f.coeff i).natDegree ≤ d) :
    ∀ i j, |((closedFormCoefficientMatrix d f i j : ℤ) : ℝ)| ≤ 2 * d * H := by
  have hb (a b m n : ℕ) (ha : a ≤ d) (hb : b = m ∨ b = n) :
      |((((a : ℤ) - (b : ℤ)) * (f.coeff m).coeff n : ℤ) : ℝ)| ≤ 2 * d * H := by
    by_cases h : (f.coeff m).coeff n = 0
    · simp [h, mul_nonneg, hH]
    have hm := (le_natDegree_of_ne_zero (show f.coeff m ≠ 0 from fun hz => h (by simp [hz]))).trans houter
    have hn := (le_natDegree_of_ne_zero h).trans (hinner m)
    
    push_cast
    rw [abs_mul]
    have hdiff : |(a : ℝ) - (b : ℝ)| ≤ (d : ℝ) := by
      rw [abs_le]
      exact ⟨by exact_mod_cast (show -(d : ℤ) ≤ (a : ℤ) - b by omega),
        by exact_mod_cast (show (a : ℤ) - b ≤ d by omega)⟩
    calc
      _ ≤ d * H := mul_le_mul hdiff (hf m n) (abs_nonneg _) (Nat.cast_nonneg _)
      _ ≤ _ := by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hH]
  intro i j
  rcases j with j | j
  · rw [closedFormCoefficientMatrix_inl]
    split_ifs
    · exact hb _ _ _ _ j.2.isLt.le (.inr rfl)
    · simp [mul_nonneg, hH]
  · rw [closedFormCoefficientMatrix_inr]
    split_ifs
    · rw [Int.cast_neg, abs_neg]
      exact hb _ _ _ _ j.1.isLt.le (.inl rfl)
    · simp [mul_nonneg, hH]

/-- Expansion of a selected determinant gives a coefficient-controlled integer
witness bound, uniformly over all choices of rows and columns. -/
theorem closedForm_integer_minor_bound
    (d r : ℕ) (f : ℤ[X][X]) (H : ℝ) (hH : 0 ≤ H)
    (hf : BivariateCoefficientBound f H) (houter : f.natDegree ≤ d)
    (hinner : ∀ i, (f.coeff i).natDegree ≤ d)
    (a : Fin r → ℕ × ℕ) (c : Fin r → ClosedFormColumns d) :
    |((((closedFormCoefficientMatrix d f).submatrix a c).det : ℤ) : ℝ)| ≤
      (r.factorial : ℝ) * (2 * d * H) ^ r := by
  have he := closedFormCoefficientMatrix_entry_bound d f H hH hf houter hinner
  have hb := Matrix.det_le (abv := AbsoluteValue.abs)
    (A := ((closedFormCoefficientMatrix d f).submatrix a c).map (Int.castRingHom ℝ))
    (fun i j => he (a i) (c j))
  have hd : (((closedFormCoefficientMatrix d f).submatrix a c).map (Int.castRingHom ℝ)).det =
      ((((closedFormCoefficientMatrix d f).submatrix a c).det : ℤ) : ℝ) :=
    ((Int.castRingHom ℝ).map_det _).symm
  rw [hd] at hb
  simpa [nsmul_eq_mul] using hb

end
end CCDN
