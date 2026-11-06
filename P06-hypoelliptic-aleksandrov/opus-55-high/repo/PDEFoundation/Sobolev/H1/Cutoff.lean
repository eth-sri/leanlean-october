module

public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Cutoff

/-!
# Quantitative smooth cutoffs in `H¹`

This file is the exact `p = 2` facade over the generic cutoff multiplier API.
It keeps the chosen value and gradient representatives literal, including the
formula for multiplication by a squared cutoff.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

namespace H1Function

variable {d : ℕ}
variable {U inner outer : Set (Vec d)}
variable {K : ℝ}

/-- Multiply an `H¹` representative by a quantitative smooth cutoff. -/
noncomputable def mulCutoff
    (u : H1Function U)
    (η : QuantitativeSmoothCutoff inner outer K) :
    H1Function U :=
  (u.toW1pFunction.mulCutoff η (by norm_num)).toH1Function

variable (u : H1Function U) (η : QuantitativeSmoothCutoff inner outer K)

@[simp]
theorem mulCutoff_toFun
     :
    (u.mulCutoff η).toFun = fun x => η.toFun x * u x := by
  aesop

@[simp]
theorem mulCutoff_grad
     :
    (u.mulCutoff η).grad =
      fun x =>
        η.toFun x • u.grad x +
          u x • classicalGradient η.toFun x := by
  aesop

/-- Exact value representative for multiplication by a squared cutoff. -/
@[simp]
theorem mulCutoff_sq_toFun
     :
    (u.mulCutoff η.sq).toFun = fun x => η x ^ 2 * u x := by
  simp

/-- Exact gradient representative for multiplication by a squared cutoff. -/
theorem mulCutoff_sq_grad
     :
    (u.mulCutoff η.sq).grad =
      fun x =>
        η x ^ 2 • u.grad x +
          (2 * η x * u x) • classicalGradient η.toFun x := by
  simpa only [mulCutoff, W1pFunction.toH1Function_grad,
    H1Function.toW1pFunction_grad,
    H1Function.toW1pFunction_apply] using
    u.toW1pFunction.mulCutoff_sq_grad η _

end H1Function

end PDE
