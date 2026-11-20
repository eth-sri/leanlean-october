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

/-- `(τ, y) ↦ (r₁ - τ, y)`. -/
def reverseTimeMap {n : ℕ} (r₁ : ℝ) : TimeVelocity n → TimeVelocity n :=
  fun z => (r₁ - z.1, z.2)

/-- Pullback of a scalar field by `reverseTimeMap r₁`. -/
def reverseTimeScalar {n : ℕ} (r₁ : ℝ)
    (f : TimeVelocity n → ℝ) : TimeVelocity n → ℝ :=
  fun z => f (reverseTimeMap r₁ z)

/-- Pullback of a time--space matrix coefficient by reverse time. -/
def reverseTimeCoefficient {n : ℕ} (r₁ : ℝ)
    (a : CoefficientField n) : CoefficientField n :=
  fun τ y => a (r₁ - τ) y

/-- Pullback of a time--space vector coefficient by reverse time. -/
def reverseTimeVectorCoefficient {n : ℕ} (r₁ : ℝ)
    (b : ℝ → PDE.Vec n → PDE.Vec n) : ℝ → PDE.Vec n → PDE.Vec n :=
  fun τ y => b (r₁ - τ) y

/-- Pullback of a curried scalar coefficient or source by reverse time. -/
def reverseTimeScalarCoefficient {n : ℕ} (r₁ : ℝ)
    (q : ℝ → PDE.Vec n → ℝ) : ℝ → PDE.Vec n → ℝ :=
  fun τ y => q (r₁ - τ) y

/-- Evaluation of `reverseTimeMap`. -/
@[simp] theorem reverseTimeMap_apply {n : ℕ} (r₁ : ℝ) (z : TimeVelocity n) :
    reverseTimeMap r₁ z = (r₁ - z.1, z.2) :=
  rfl

/-- Evaluation of the reverse-time scalar pullback. -/
@[simp] theorem reverseTimeScalar_apply {n : ℕ} (r₁ : ℝ)
    (f : TimeVelocity n → ℝ) (z : TimeVelocity n) :
    reverseTimeScalar r₁ f z = f (reverseTimeMap r₁ z) :=
  rfl

/-- Evaluation of the reverse-time matrix-coefficient pullback. -/
@[simp] theorem reverseTimeCoefficient_apply {n : ℕ} (r₁ : ℝ)
    (a : CoefficientField n) (τ : ℝ) (y : PDE.Vec n) :
    reverseTimeCoefficient r₁ a τ y = a (r₁ - τ) y :=
  rfl

/-- Evaluation of the reverse-time vector-coefficient pullback. -/
@[simp] theorem reverseTimeVectorCoefficient_apply {n : ℕ} (r₁ : ℝ)
    (b : ℝ → PDE.Vec n → PDE.Vec n) (τ : ℝ) (y : PDE.Vec n) :
    reverseTimeVectorCoefficient r₁ b τ y = b (r₁ - τ) y :=
  rfl

/-- Evaluation of the reverse-time scalar-coefficient pullback. -/
@[simp] theorem reverseTimeScalarCoefficient_apply {n : ℕ} (r₁ : ℝ)
    (q : ℝ → PDE.Vec n → ℝ) (τ : ℝ) (y : PDE.Vec n) :
    reverseTimeScalarCoefficient r₁ q τ y = q (r₁ - τ) y :=
  rfl

/-- The vector with `j` component `∑ i, ∂ᵢ aᵢⱼ`, at a fixed time. -/
def scalarSpatialCoefficientDivergence {n : ℕ}
    (a : CoefficientField n) (z : TimeVelocity n) : PDE.Vec n :=
  fun j => ∑ i : Fin n,
    (fderiv ℝ (fun y : PDE.Vec n => a z.1 y i j) z.2) (PDE.basisVec i)

/-- `dᴿ_j = ∑ᵢ ∂ᵢaᴿ_ij - bᴿ_j`, with the manuscript's row--column order. -/
def reverseTimeDivergenceDrift {n : ℕ} (r₁ : ℝ)
    (a : CoefficientField n) (b : ℝ → PDE.Vec n → PDE.Vec n) :
    ℝ → PDE.Vec n → PDE.Vec n :=
  fun τ y => scalarSpatialCoefficientDivergence
      (reverseTimeCoefficient r₁ a) (τ, y) -
    reverseTimeVectorCoefficient r₁ b τ y

/-- Reverse time commutes with the fixed-time coefficient divergence. -/
theorem scalarSpatialCoefficientDivergence_reverseTimeCoefficient
    {n : ℕ} (r₁ : ℝ) (a : CoefficientField n) (z : TimeVelocity n) :
    scalarSpatialCoefficientDivergence (reverseTimeCoefficient r₁ a) z =
      scalarSpatialCoefficientDivergence a (reverseTimeMap r₁ z) :=
  rfl

end HypoellipticAleksandrov.Parabolic
