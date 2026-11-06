module

public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Product
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Smooth multipliers on representative-level `H¹`

This file is the `p = 2` facade over the generic representative-level
`W^{1,p}` multiplier API. Every constructor and estimate is transported
through the exact equivalence between `H1Function U` and
`W1pFunction U 2`; the distributional product rule is not reproved here.

The stored gradient is

`φ Du + u classicalGradient φ`.

The coordinate `L²` estimates retain coefficient one in the triangle
inequality, with no dimension-dependent or numerical loss.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

variable (u : H1Function U) {φ : Vec d → ℝ} (hφ : ContDiff ℝ PDE.smoothOrder φ)

variable (hφTop : MemLpOn U ∞ φ) (hDφTop : ∀ i : Fin d, MemLpOn U ∞ (fun x => classicalGradient φ x i))

/-- Multiply an `H¹` representative by a smooth multiplier whose value and
coordinate gradient are essentially bounded on the domain.

This is the LIH-compatible `p = 2` specialization of
`W1pFunction.mulContDiffMemLpTop`.
-/
noncomputable def mulContDiffMemLpTop

     :
    H1Function U :=
  (W1pFunction.mulContDiffMemLpTop
    u.toW1pFunction hφ hφTop hDφTop).toH1Function





variable (hφCompact : HasCompactSupport φ)

/-- A smooth compactly supported multiplier preserves representative-level
`H¹`; compact support supplies the required `L∞` hypotheses. -/
noncomputable def mulContDiffHasCompactSupport

     :
    H1Function U :=
  (W1pFunction.mulContDiffHasCompactSupport
    u.toW1pFunction hφ hφCompact).toH1Function

@[simp]
theorem mulContDiffHasCompactSupport_toFun

     :
    (u.mulContDiffHasCompactSupport hφ hφCompact).toFun =
      fun x => φ x * u x := by
  rfl



end H1Function

end PDE
