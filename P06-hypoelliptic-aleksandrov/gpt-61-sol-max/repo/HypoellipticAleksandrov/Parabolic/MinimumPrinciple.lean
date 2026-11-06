module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.Parabolic.Operator

/-!
# Pointwise parabolic minimum principle

This module proves the one-sided pointwise calculus statement behind the classical
forward parabolic minimum principle. At a local minimum relative to all earlier times,
the time derivative is nonpositive and the velocity Hessian is positive semidefinite.
Consequently, a positive semidefinite coefficient matrix gives the expected sign for
the forward parabolic operator.

The regularity assumption is pointwise `ContDiffAt ℝ 2 u z`. The second-derivative
argument is localized along affine lines through `z`; no global smoothness assumption
or comparison principle is used.

## Main results

* `velocityHessian_posSemidef_of_past_localMin`: positivity of the velocity Hessian.
* `timeDerivative_nonpos_of_past_localMin`: the one-sided time-derivative sign.
* `parabolicOperator_nonpos_of_past_localMin`: the pointwise operator sign.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open Matrix
open scoped MatrixOrder

/-- The trace of the product of two real positive semidefinite matrices is nonnegative. -/
theorem trace_mul_nonneg_of_posSemidef
    {d : ℕ} {A H : PDE.Mat d}
    (hA : A.PosSemidef) (hH : H.PosSemidef) :
    0 ≤ (A * H).trace := by
  classical
  let S : PDE.Mat d := CFC.sqrt H
  have hS : S.PosSemidef := by
    dsimp [S]
    exact CFC.sqrt_nonneg H |>.posSemidef

  calc
    0 ≤ (S * A * Sᴴ).trace := (hA.mul_mul_conjTranspose_same S).trace_nonneg
    _ = (S * A * S).trace := by rw [hS.isHermitian.eq]
    _ = (A * S * S).trace := (Matrix.trace_mul_cycle A S S).symm
    _ = (A * (S * S)).trace := by rw [Matrix.mul_assoc]
    _ = (A * H).trace := by rw [show S * S = H by
      dsimp [S]
      exact CFC.sqrt_mul_sqrt_self H hH.nonneg]

end HypoellipticAleksandrov.Parabolic
