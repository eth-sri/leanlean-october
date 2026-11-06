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
    (u : TimeVelocity d → ℝ) (z : TimeVelocity d) : ℝ :=
  timeDerivative u z - matrixContraction (coefficientAt A z) (velocityHessian u z)

/-- Evaluation of the forward parabolic operator. -/
@[simp]
theorem parabolicOperator_apply {d : ℕ} (A : CoefficientField d)
    (u : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    parabolicOperator A u z =
      timeDerivative u z - matrixContraction (coefficientAt A z) (velocityHessian u z) :=
  rfl

/-- A function is a subsolution when the forward operator is bounded by its source on a set. -/
def IsParabolicSubsolutionOn {d : ℕ} (A : CoefficientField d)
    (f u : TimeVelocity d → ℝ) (s : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ s, parabolicOperator A u z ≤ f z

namespace IsParabolicSubsolutionOn

end IsParabolicSubsolutionOn

end HypoellipticAleksandrov.Parabolic
