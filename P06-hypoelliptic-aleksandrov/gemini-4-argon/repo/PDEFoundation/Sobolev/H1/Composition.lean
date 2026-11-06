module

public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Composition

@[expose] public section

open scoped ENNReal

/-!
# Bounded-derivative composition in `H¹`

This file is the exact `p = 2` facade for the generic `W^{1,p}` composition
theorem.  It preserves the concrete value and gradient representatives used
by the application repositories; no analytic argument is repeated here.
-/

namespace PDE

open MeasureTheory

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

/- The `p = 2` weak chain rule, stated directly on the representative-level
`H¹` carrier.  This is an exact transport of the generic finite-exponent
theorem. -/
theorem hasWeakGradient_comp_contDiff_of_deriv_bounded
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U)
    {G } (hG : ContDiff ℝ 1 G)
    {M } (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    HasWeakGradientOn U
      (fun x => G (u.toFun x))
      (fun x i => deriv G (u.toFun x) * u.grad x i) := by
  simpa only [toW1pFunction_toFun, toW1pFunction_grad] using
    W1pFunction.hasWeakGradient_comp_contDiff_of_deriv_bounded
      hU (by norm_num) (by norm_num) u.toW1pFunction hG hM hderiv

/- Compose an `H¹` representative with a `C¹` real function whose derivative
is bounded by `M`. -/
end H1Function

end PDE
