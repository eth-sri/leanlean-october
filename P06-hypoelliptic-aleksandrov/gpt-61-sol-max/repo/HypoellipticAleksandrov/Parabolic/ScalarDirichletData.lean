module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import PDEFoundation.Calculus.RegularityOrder


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

/-- A supplied ambient function is C^∞ on an open neighbourhood of `K`. -/
def IsSmoothOnNeighborhood
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (K : Set E) : Prop :=
  ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ ContDiffOn ℝ PDE.smoothOrder f V

variable {n : ℕ}

variable (a : CoefficientField n) (b : PDE.TimeVectorField n) (c : PDE.TimeScalarField n) (u : HypoellipticAleksandrov.Parabolic.ScalarField n) (z : TimeVelocity n)

/-- The backward scalar operator with its source zero-order term. -/
def scalarParabolicZeroOrderOperator
     : ℝ :=
  scalarParabolicOperator a b u z + c z.1 z.2 * u z

/-- Evaluation of the scalar parabolic operator with its zero-order term. -/
@[simp] theorem scalarParabolicZeroOrderOperator_apply
     :
    scalarParabolicZeroOrderOperator a b c u z =
      scalarTimeDerivative u z +
        matrixContraction (a z.1 z.2) (scalarSpatialHessian u z) +
        PDE.vecDot (b z.1 z.2) (scalarSpatialGradient u z) +
        c z.1 z.2 * u z :=
  rfl

/-- A supplied classical solution of the backward scalar Dirichlet problem. -/
def IsClassicalBackwardDirichletSolution
    (r₀ r₁ : ℝ) (Ω : PDE.VelocityRegion n)
    (a : CoefficientField n)
    (b : PDE.TimeVectorField n)
    (c F : PDE.TimeScalarField n)
    (phi : PDE.ScalarField n) (h u : HypoellipticAleksandrov.Parabolic.ScalarField n) : Prop :=
  ContinuousOn u (scalarParabolicClosedCylinder r₀ r₁ Ω) ∧
    IsScalarC12On u (scalarParabolicOpenCylinder r₀ r₁ Ω) ∧
    (∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      scalarParabolicZeroOrderOperator a b c u z = F z.1 z.2) ∧
    (∀ y ∈ closure Ω, u (r₁, y) = phi y) ∧
    (∀ z ∈ scalarParabolicLateralFace r₀ r₁ Ω, u z = h z)

end HypoellipticAleksandrov.Parabolic
