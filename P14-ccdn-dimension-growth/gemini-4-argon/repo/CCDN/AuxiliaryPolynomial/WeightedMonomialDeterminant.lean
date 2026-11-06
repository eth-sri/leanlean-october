/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.MonomialEvaluationMatrix
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Int

/-! Archimedean determinant bounds retaining each monomial's own degree.
Their exponent is the sum of column degrees, not rank times the cutoff. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset Matrix

/-- A nonzero integer determinant has the sharp sum-of-degrees logarithmic
upper bound. -/
theorem weighted_evaluation_det_log_bound {n s : ℕ}
    (mon : Fin s → (Fin n →₀ ℕ)) (z : Fin s → (Fin n → ℤ))
    {B : ℝ} (hB : 1 ≤ B) (hz : ∀ i, InBox (z i) B)
    (hne : (evaluationMatrix mon z).det ≠ 0) :
    Real.log |((evaluationMatrix mon z).det : ℝ)| ≤
      Real.log (s.factorial : ℝ) +
        (∑ j, ((Finsupp.degree (mon j) : ℕ) : ℝ)) * Real.log B := by
  classical
  let A := (evaluationMatrix mon z).map (Int.castRingHom ℝ)
  let abv : AbsoluteValue ℝ ℝ := AbsoluteValue.abs
  have hh : |((evaluationMatrix mon z).det : ℝ)| ≤
      (s.factorial : ℝ) * B ^ (∑ j, Finsupp.degree (mon j)) := by
    have he : A.det = ((evaluationMatrix mon z).det : ℝ) :=
      ((Int.castRingHom ℝ).map_det _).symm
    rw [← he, ← prod_pow_eq_pow_sum]
    calc
      |A.det| ≤ ∑ σ : Equiv.Perm (Fin s), abv (Equiv.Perm.sign σ • ∏ j, A (σ j) j) := by
        rw [Matrix.det_apply]; exact abv.sum_le _ _
      _ = ∑ σ : Equiv.Perm (Fin s), ∏ j, |A (σ j) j| :=
        sum_congr rfl fun σ _ => by rw [abv.map_units_int_smul, abv.map_prod]; rfl
      _ ≤ ∑ _σ : Equiv.Perm (Fin s), ∏ j, B ^ Finsupp.degree (mon j) :=
        sum_le_sum fun σ _ => prod_le_prod₀ (fun j _ => abs_nonneg _)
          (fun j _ => abs_monomial_value_le (mon j) (z (σ j)) hB (hz (σ j)) le_rfl)
      _ = _ := by simp [Fintype.card_perm]
  have hB0 : 0 < B := by linarith
  have hfac : (0 : ℝ) < s.factorial := by exact_mod_cast Nat.factorial_pos s
  have hlog := Real.log_le_log (abs_pos.mpr (by exact_mod_cast hne)) hh
  rw [Real.log_mul hfac.ne' (pow_pos hB0 _).ne', Real.log_pow] at hlog
  simpa only [Nat.cast_sum] using hlog

end
end CCDN
