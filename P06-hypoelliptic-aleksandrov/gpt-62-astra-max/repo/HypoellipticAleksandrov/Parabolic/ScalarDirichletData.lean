module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical

@[expose] public section

noncomputable section

/-!
# Scalar parabolic Dirichlet data

This module records the supplied-data language for the bounded scalar
parabolic Dirichlet problem.  It defines neighbourhood smoothness, the
zero-order operator, terminal-corner compatibility, and the classical
solution predicate; it proves no existence or regularity result.
-/

namespace HypoellipticAleksandrov.Parabolic

variable {n : ℕ} (r₀ r₁ : ℝ) (Ω : Set (PDE.Vec n)) (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n) (c : ℝ → PDE.Vec n → ℝ) (u : TimeVelocity n → ℝ)
    (z : TimeVelocity n)

include a b c u z in
/-- The backward scalar operator with its source zero-order term. -/
def scalarParabolicZeroOrderOperator : ℝ :=
  scalarParabolicOperator a b u z + c z.1 z.2 * u z

/-- Evaluation of the scalar parabolic operator with its zero-order term. -/
@[simp] theorem scalarParabolicZeroOrderOperator_apply :
    scalarParabolicZeroOrderOperator a b c u z =
      scalarTimeDerivative u z +
        matrixContraction (a z.1 z.2) (scalarSpatialHessian u z) +
        PDE.vecDot (b z.1 z.2) (scalarSpatialGradient u z) +
        c z.1 z.2 * u z :=
  rfl

include r₀ r₁ Ω a b in
/-- A supplied classical solution of the backward scalar Dirichlet problem. -/
def IsClassicalBackwardDirichletSolution
    (c F : ℝ → PDE.Vec n → ℝ)
    (phi : PDE.Vec n → ℝ) (h u : TimeVelocity n → ℝ) : Prop :=
  ContinuousOn u (scalarParabolicClosedCylinder r₀ r₁ Ω) ∧
    IsScalarC12On u (scalarParabolicOpenCylinder r₀ r₁ Ω) ∧
    (∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      scalarParabolicZeroOrderOperator a b c u z = F z.1 z.2) ∧
    (∀ y ∈ closure Ω, u (r₁, y) = phi y) ∧
    (∀ z ∈ scalarParabolicLateralFace r₀ r₁ Ω, u z = h z)

end HypoellipticAleksandrov.Parabolic
