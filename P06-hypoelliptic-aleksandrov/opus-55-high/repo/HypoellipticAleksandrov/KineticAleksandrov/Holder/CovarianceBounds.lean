module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covariance
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! # Positive definiteness and Loewner bounds for the kinetic covariance -/

@[expose] public section


namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Matrix
open scoped MatrixOrder

variable {a b c : ℝ}

/-- The two-dimensional Sylvester test, stated in literal scalar block coordinates. -/
theorem posDef_two_of_det  (ha : 0 < a) (hdet : 0 < a * b - c ^ 2) :
    (!![a, c; c, b] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro x hx
    have hn : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      ext i
      fin_cases i <;> simp [h]
    simp [dotProduct]
    rcases hn with h0 | h1
    · by_cases h1 : x 1 = 0
      · simp only [h1]
        nlinarith [sq_pos_of_ne_zero h0]
      · have hp := mul_pos hdet (sq_pos_of_ne_zero h1)
        nlinarith [sq_nonneg (a * x 0 + c * x 1)]
    · have hp := mul_pos hdet (sq_pos_of_ne_zero h1)
      nlinarith [sq_nonneg (a * x 0 + c * x 1)]

/-- Symmetric diagonal dominance implies positive semidefiniteness in scalar block coordinates. -/
theorem posSemidef_two_of_diagonal  (ha : |c| ≤ a) (hb : |c| ≤ b) :
    (!![a, c; c, b] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro x
    simp [dotProduct]
    have h0 := mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg (x 0))
    have h1 := mul_nonneg (sub_nonneg.mpr hb) (sq_nonneg (x 1))
    rcases le_total 0 c with hc | hc
    · rw [abs_of_nonneg hc] at h0 h1
      have h2 := mul_nonneg hc (sq_nonneg (x 0 + x 1))
      nlinarith
    · rw [abs_of_nonpos hc] at h0 h1
      have h2 := mul_nonneg (neg_nonneg.mpr hc) (sq_nonneg (x 0 - x 1))
      nlinarith

/-- The dimensionless covariance is positive definite on the entire closed cutoff strip. -/
theorem posDef_ghat {lam theta : ℝ} (hlam : 0 < lam)
    (ht : -(1 / 128 : ℝ) ≤ theta) : (ghat lam theta).PosDef := by
  have hbase : 0 < (1 + theta ^ 2) / 64 + theta ^ 3 / 3 := by
    nlinarith [sq_nonneg theta]
  have hdet : 0 < 1 / 4096 + theta / 64 + theta ^ 3 / 192 + theta ^ 4 / 12 := by
    nlinarith [sq_nonneg (theta ^ 2)]
  apply posDef_two_of_det
  · convert mul_pos hlam hbase using 1
    ring
  · have hp := mul_pos (sq_pos_of_pos hlam) hdet
    linarith

end HypoellipticAleksandrov.KineticAleksandrov.Holder
