module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import HypoellipticAleksandrov.Parabolic.LocalClassical

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
  ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ ContDiffOn ℝ (⊤ : ℕ∞) f V

/-- A globally smooth function is smooth near every set. -/
theorem _root_.ContDiff.onNeighborhood
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {K : Set E} (h : ContDiff ℝ (⊤ : ℕ∞) f) :
    IsSmoothOnNeighborhood f K := ⟨Set.univ, isOpen_univ, Set.subset_univ _, h.contDiffOn⟩

/-- Smoothness of a curried coefficient on a neighbourhood of a closed cylinder. -/
abbrev IsSmoothOnClosedCylinder {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (r₀ r₁ : ℝ) (Ω : Set (PDE.Vec d))
    (f : ℝ → PDE.Vec d → F) : Prop :=
  IsSmoothOnNeighborhood (fun z => f z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)

section
variable {n : ℕ} (a : CoefficientField n) (b : ℝ → PDE.Vec n → PDE.Vec n) (c : ℝ → PDE.Vec n → ℝ)
  (u : TimeVelocity n → ℝ) (z : TimeVelocity n)
include n a b c u z

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

end

/-- A supplied classical solution of the backward scalar Dirichlet problem. -/
def IsClassicalBackwardDirichletSolution {n : ℕ}
    (r₀ r₁ : ℝ) (Ω : Set (PDE.Vec n))
    (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c F : ℝ → PDE.Vec n → ℝ)
    (phi : PDE.Vec n → ℝ) (h u : TimeVelocity n → ℝ) : Prop :=
  ContinuousOn u (scalarParabolicClosedCylinder r₀ r₁ Ω) ∧
    IsScalarC12On u (scalarParabolicOpenCylinder r₀ r₁ Ω) ∧
    (∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      scalarParabolicZeroOrderOperator a b c u z = F z.1 z.2) ∧
    (∀ y ∈ closure Ω, u (r₁, y) = phi y) ∧
    (∀ z ∈ scalarParabolicLateralFace r₀ r₁ Ω, u z = h z)

end HypoellipticAleksandrov.Parabolic
