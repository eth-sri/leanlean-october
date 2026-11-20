module

public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Product

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

/-- Multiply an `H¹` representative by a smooth multiplier whose value and
coordinate gradient are essentially bounded on the domain.

This is the LIH-compatible `p = 2` specialization of
`W1pFunction.mulContDiffMemLpTop`.
-/
noncomputable def mulContDiffMemLpTop
    (u : H1Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφTop : MemLpOn U ∞ φ)
    (hDφTop : ∀ i : Fin d,
      MemLpOn U ∞
        (fun x => classicalGradient φ x i)) :
    H1Function U :=
  (W1pFunction.mulContDiffMemLpTop
    u.toW1pFunction hφ hφTop hDφTop).toH1Function

@[simp]
theorem mulContDiffMemLpTop_toFun
    (u : H1Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφTop : MemLpOn U ∞ φ)
    (hDφTop : ∀ i : Fin d,
      MemLpOn U ∞
        (fun x => classicalGradient φ x i)) :
    (u.mulContDiffMemLpTop hφ hφTop hDφTop).toFun =
      fun x => φ x * u x := by
  simp only [mulContDiffMemLpTop,
    W1pFunction.toH1Function_toFun,
    W1pFunction.mulContDiffMemLpTop_toFun,
    H1Function.toW1pFunction_apply]

@[simp]
theorem mulContDiffMemLpTop_grad
    (u : H1Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφTop : MemLpOn U ∞ φ)
    (hDφTop : ∀ i : Fin d,
      MemLpOn U ∞
        (fun x => classicalGradient φ x i)) :
    (u.mulContDiffMemLpTop hφ hφTop hDφTop).grad =
      fun x =>
        φ x • u.grad x + u x • classicalGradient φ x := by
  simp only [mulContDiffMemLpTop,
    W1pFunction.toH1Function_grad,
    W1pFunction.mulContDiffMemLpTop_grad,
    H1Function.toW1pFunction_grad,
    H1Function.toW1pFunction_apply]

/-- A smooth compactly supported multiplier preserves representative-level
`H¹`; compact support supplies the required `L∞` hypotheses. -/
noncomputable def mulContDiffHasCompactSupport
    (u : H1Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) :
    H1Function U :=
  (W1pFunction.mulContDiffHasCompactSupport
    u.toW1pFunction hφ hφCompact).toH1Function

@[simp]
theorem mulContDiffHasCompactSupport_toFun
    (u : H1Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) :
    (u.mulContDiffHasCompactSupport hφ hφCompact).toFun =
      fun x => φ x * u x := by
  simp only [mulContDiffHasCompactSupport,
    W1pFunction.toH1Function_toFun,
    W1pFunction.mulContDiffHasCompactSupport_toFun,
    H1Function.toW1pFunction_apply]

@[simp]
theorem mulContDiffHasCompactSupport_grad
    (u : H1Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) :
    (u.mulContDiffHasCompactSupport hφ hφCompact).grad =
      fun x =>
        φ x • u.grad x + u x • classicalGradient φ x := by
  simp only [mulContDiffHasCompactSupport,
    W1pFunction.toH1Function_grad,
    W1pFunction.mulContDiffHasCompactSupport_grad,
    H1Function.toW1pFunction_grad,
    H1Function.toW1pFunction_apply]

end H1Function

end PDE
