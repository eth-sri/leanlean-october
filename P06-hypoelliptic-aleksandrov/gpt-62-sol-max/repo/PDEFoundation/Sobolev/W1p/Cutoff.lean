module

public import PDEFoundation.Sobolev.Cutoff.Basic
public import PDEFoundation.Sobolev.W1p.Product

/-!
# Multiplication by quantitative smooth cutoffs

This file specializes the existing smooth compact-support product rule to
`QuantitativeSmoothCutoff`. The weak product rule is not reproved: the
constructor delegates directly to
`W1pFunction.mulContDiffHasCompactSupport`.

The resulting value and coordinate-gradient estimates retain the explicit
coefficients `1` and `ENNReal.ofReal K`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

namespace W1pFunction

variable {d : ℕ}
variable {U inner outer : Set (Vec d)}
variable {p : ℝ≥0∞}
variable {K : ℝ}

/-- Multiply a representative-level Sobolev function by a quantitative smooth
cutoff.

The exponent assumption is explicit. Internally it supplies the local
integrability hypothesis needed by the existing smooth compact-support
product rule. -/
noncomputable def mulCutoff
    (u : W1pFunction U p)
    (η : QuantitativeSmoothCutoff inner outer K)
    (hp : 1 ≤ p) :
    W1pFunction U p := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  exact
    u.mulContDiffHasCompactSupport
      η.smooth η.hasCompactSupport

@[simp]
theorem mulCutoff_toFun
    (u : W1pFunction U p)
    (η : QuantitativeSmoothCutoff inner outer K)
    (hp : 1 ≤ p) :
    (u.mulCutoff η hp).toFun =
      fun x => η.toFun x * u x := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  change
    (u.mulContDiffHasCompactSupport
      η.smooth η.hasCompactSupport).toFun =
        fun x => η.toFun x * u x
  exact
    u.mulContDiffHasCompactSupport_toFun
      η.smooth η.hasCompactSupport

@[simp]
theorem mulCutoff_grad
    (u : W1pFunction U p)
    (η : QuantitativeSmoothCutoff inner outer K)
    (hp : 1 ≤ p) :
    (u.mulCutoff η hp).grad =
      fun x =>
        η.toFun x • u.grad x +
          u x • classicalGradient η.toFun x := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  change
    (u.mulContDiffHasCompactSupport
      η.smooth η.hasCompactSupport).grad =
        fun x =>
          η.toFun x • u.grad x +
            u x • classicalGradient η.toFun x
  exact
    u.mulContDiffHasCompactSupport_grad
      η.smooth η.hasCompactSupport

/-- Multiplication by the square of a cutoff has the expected squared value
representative. -/
@[simp]
theorem mulCutoff_sq_toFun
    (u : W1pFunction U p)
    (η : QuantitativeSmoothCutoff inner outer K)
    (hp : 1 ≤ p) :
    (u.mulCutoff η.sq hp).toFun =
      fun x => η x ^ 2 * u x := by
  rw [mulCutoff_toFun, QuantitativeSmoothCutoff.sq_toFun]

/-- Exact product-rule gradient for multiplication by a squared cutoff. -/
theorem mulCutoff_sq_grad
    (u : W1pFunction U p)
    (η : QuantitativeSmoothCutoff inner outer K)
    (hp : 1 ≤ p) :
    (u.mulCutoff η.sq hp).grad =
      fun x =>
        η x ^ 2 • u.grad x +
          (2 * η x * u x) • classicalGradient η.toFun x := by
  rw [mulCutoff_grad]
  funext x i
  rw [QuantitativeSmoothCutoff.sq_classicalGradient]
  simp only [QuantitativeSmoothCutoff.sq_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

end W1pFunction

end PDE
