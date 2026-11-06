module

public import HypoellipticAleksandrov.Ambient.MatrixContraction
public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import HypoellipticAleksandrov.Parabolic.Derivatives

/-!
# The forward parabolic operator

This module defines the time--velocity operator with sign
`∂ₜ u - A : Dᵥ² u` and its transparent pointwise subsolution predicate.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

/-- The forward parabolic operator `∂ₜ u - A : Dᵥ² u`. -/
def parabolicOperator {d : ℕ} (A : CoefficientField d)
    (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (z : TimeVelocity d) : ℝ :=
  timeDerivative u z - matrixContraction (coefficientAt A z) (velocityHessian u z)

variable {d : ℕ} (A : CoefficientField d)

/-- Evaluation of the forward parabolic operator. -/
@[simp]
theorem parabolicOperator_apply
    (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (z : TimeVelocity d) :
    parabolicOperator A u z =
      timeDerivative u z - matrixContraction (coefficientAt A z) (velocityHessian u z) :=
  rfl

/-- A function is a subsolution when the forward operator is bounded by its source on a set. -/
def IsParabolicSubsolutionOn
    (f u : HypoellipticAleksandrov.Parabolic.ScalarField d) (s : HypoellipticAleksandrov.Parabolic.Region d) : Prop :=
  ∀ z ∈ s, parabolicOperator A u z ≤ f z



end HypoellipticAleksandrov.Parabolic
