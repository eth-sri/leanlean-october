module

public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Truncation

/-!
# Positive-part truncation in `H¹`

This file is the exact `p = 2` facade for the generic `W^{1,p}` positive-part
construction. It preserves the concrete value and gradient representatives
used by the application repositories; no analytic argument is repeated here.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

/-- Positive-part truncation of an `H¹` representative at a constant level. -/
noncomputable def positivePartSubConst
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (c : ℝ) :
    H1Function U :=
  (u.toW1pFunction.positivePartSubConst
    hU (by norm_num) (by norm_num) c).toH1Function

variable (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) (c : ℝ)

@[simp]
theorem positivePartSubConst_toFun
     :
    (u.positivePartSubConst hU c).toFun =
      fun x => max (u.toFun x - c) 0 :=
  rfl

@[simp]
theorem positivePartSubConst_grad
     :
    (u.positivePartSubConst hU c).grad =
      fun x =>
        {y | c < u.toFun y}.indicator u.grad x :=
  rfl

end H1Function

end PDE
