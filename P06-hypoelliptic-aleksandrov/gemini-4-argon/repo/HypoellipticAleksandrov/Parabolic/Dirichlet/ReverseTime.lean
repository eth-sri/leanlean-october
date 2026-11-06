module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic.Ring

/-!
# Classical reverse-time divergence rewrite

This file records the pointwise reverse-time calculation for the scalar
parabolic Dirichlet equation, including its literal coordinate divergence
form.  It does not introduce a weak or variational divergence.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace HypoellipticAleksandrov.Parabolic

/- `(τ, y) ↦ (r₁ - τ, y)`. -/
def reverseTimeMap {n } (r₁ : ℝ) : TimeVelocity n → TimeVelocity n :=
  fun z => (r₁ - z.1, z.2)

/- Pullback of a scalar field by `reverseTimeMap r₁`. -/
def reverseTimeCoefficient {n } (r₁ : ℝ)
    (a : CoefficientField n) : CoefficientField n :=
  fun τ y => a (r₁ - τ) y

/- Pullback of a time--space vector coefficient by reverse time. -/
def reverseTimeVectorCoefficient {n } (r₁ : ℝ)
    (b : ℝ → PDE.Vec n → PDE.Vec n) : ℝ → PDE.Vec n → PDE.Vec n :=
  fun τ y => b (r₁ - τ) y

/- Pullback of a curried scalar coefficient or source by reverse time. -/
def reverseTimeScalarCoefficient {n } (r₁ : ℝ)
    (q : ℝ → PDE.Vec n → ℝ) : ℝ → PDE.Vec n → ℝ :=
  fun τ y => q (r₁ - τ) y

@[simp] theorem reverseTimeMap_apply {n } (r₁ : ℝ) (z : TimeVelocity n) :
    reverseTimeMap r₁ z = (r₁ - z.1, z.2) := rfl

@[simp] theorem reverseTimeCoefficient_apply {n } (r₁ : ℝ)
    (a : CoefficientField n) (τ : ℝ) (y : PDE.Vec n) :
    reverseTimeCoefficient r₁ a τ y = a (r₁ - τ) y := rfl

@[simp] theorem reverseTimeVectorCoefficient_apply {n } (r₁ : ℝ)
    (b : ℝ → PDE.Vec n → PDE.Vec n) (τ : ℝ) (y : PDE.Vec n) :
    reverseTimeVectorCoefficient r₁ b τ y = b (r₁ - τ) y := rfl

@[simp] theorem reverseTimeScalarCoefficient_apply {n } (r₁ : ℝ)
    (q : ℝ → PDE.Vec n → ℝ) (τ : ℝ) (y : PDE.Vec n) :
    reverseTimeScalarCoefficient r₁ q τ y = q (r₁ - τ) y := rfl

/- Evaluation of `reverseTimeMap`. -/
def scalarSpatialCoefficientDivergence {n }
    (a : CoefficientField n) (z : TimeVelocity n) : PDE.Vec n :=
  fun j => ∑ i : Fin n,
    (fderiv ℝ (fun y : PDE.Vec n => a z.1 y i j) z.2) (PDE.basisVec i)

/- `dᴿ_j = ∑ᵢ ∂ᵢaᴿ_ij - bᴿ_j`, with the manuscript's row--column order. -/
def reverseTimeDivergenceDrift {n } (r₁ : ℝ)
    (a : CoefficientField n) (b : ℝ → PDE.Vec n → PDE.Vec n) :
    ℝ → PDE.Vec n → PDE.Vec n :=
  fun τ y => scalarSpatialCoefficientDivergence
      (reverseTimeCoefficient r₁ a) (τ, y) -
    reverseTimeVectorCoefficient r₁ b τ y

theorem scalarSpatialCoefficientDivergence_reverseTimeCoefficient
    {n } (r₁ : ℝ) (a : CoefficientField n) (z : TimeVelocity n) :
    scalarSpatialCoefficientDivergence (reverseTimeCoefficient r₁ a) z =
      scalarSpatialCoefficientDivergence a (reverseTimeMap r₁ z) := rfl

end HypoellipticAleksandrov.Parabolic
