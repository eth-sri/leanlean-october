/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.ClosedFormEntry
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

private lemma closedFormCoefficientMatrix_entry_bound (d : ℕ) (f : ℤ[X][X]) (H : ℝ) (hH : 0 ≤ H) (hf : BivariateCoefficientBound f H)
    (houter : f.natDegree ≤ d) (hinner : ∀ i, (f.coeff i).natDegree ≤ d) (i) (j : ClosedFormColumns d) :
    |((closedFormCoefficientMatrix d f i j : ℤ):ℝ)| ≤ 2*d*H := by
  rw [closedFormEntry_apply]; dsimp only
  let u := (closedFormEntry i j).1
  by_cases hz : (f.coeff u.1).coeff u.2 = 0
  · change |(((closedFormEntry i j).2 * (f.coeff u.1).coeff u.2 : ℤ):ℝ)| ≤ _
    simp [hz]; positivity
  have h1 : u.1 ≤ d := by by_contra! h; apply hz; rw [coeff_eq_zero_of_natDegree_lt (houter.trans_lt h),coeff_zero]
  have h2 := (le_natDegree_of_ne_zero hz).trans (hinner u.1)
  have hw : |(closedFormEntry i j).2| ≤ 2*(d:ℤ) := by
    apply abs_le.mpr; rcases j with ⟨a,b⟩|⟨a,b⟩ <;> simp only [u,closedFormEntry] at * <;> split_ifs <;> omega
  push_cast; rw [abs_mul]; apply mul_le_mul _ (hf _ _) (abs_nonneg _) (by positivity)
  exact_mod_cast hw

variable (d r : ℕ) (f : ℤ[X][X]) (H : ℝ) (hH : 0 ≤ H) (hf : BivariateCoefficientBound f H)
    (houter : f.natDegree ≤ d) (hinner : ∀ i, (f.coeff i).natDegree ≤ d)

include hH hf houter hinner in
/-- Expansion of a selected determinant gives a coefficient-controlled integer
witness bound, uniformly over all choices of rows and columns. -/
theorem closedForm_integer_minor_bound
    (a : Fin r → ℕ × ℕ) (c : Fin r → ClosedFormColumns d) :
    |((((closedFormCoefficientMatrix d f).submatrix a c).det : ℤ) : ℝ)| ≤
      (r.factorial : ℝ) * (2 * d * H) ^ r := by
  have hb := Matrix.det_le (abv := AbsoluteValue.abs)
    (A := ((closedFormCoefficientMatrix d f).submatrix a c).map (Int.castRingHom ℝ))
    (fun i j => (closedFormCoefficientMatrix_entry_bound d f H hH hf houter hinner) (a i) (c j))
  have hd : (((closedFormCoefficientMatrix d f).submatrix a c).map (Int.castRingHom ℝ)).det =
      ((((closedFormCoefficientMatrix d f).submatrix a c).det : ℤ) : ℝ) :=
    ((Int.castRingHom ℝ).map_det _).symm
  simp_all

end
end CCDN
