module

public import HypoellipticAleksandrov.Parabolic.KineticClassical

/-!
# Kinetic Aleksandrov operators

This module records the three operator surfaces used by the kinetic
Aleksandrov source.  `backwardOperator` is the full kinetic operator
`∂ₜ + v · ∇ₓ - A : Dᵥ²`, while `transportedForwardOperator` is the forward
operator `∂σ + B : Dᵧ² + b(y) · ∇z`.

For the transported operator, `KineticPoint n` is read as the ordered triple
`(σ, y, z)`: its `position` field is the diffused `y` coordinate and its
`velocity` field is the transported `z` coordinate.  The derivative APIs are
the existing ones on `KineticPoint`; no second point or derivative hierarchy
is introduced.  The W/I domain and structural alternatives belong to a
separate setting conditions, not to these literal operator definitions.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov
open HypoellipticAleksandrov.Parabolic

/-- A full matrix coefficient depending on time, position, and velocity. -/
abbrev FullKineticCoefficient (d : ℕ) :=
  ℝ → PDE.Vec d → PDE.Vec d → PDE.Mat d

section
variable {d : ℕ} (A : FullKineticCoefficient d)
include A

/-- Evaluation of a full kinetic coefficient at an explicit kinetic point. -/
def fullKineticCoefficientAt
    (z : KineticPoint d) : PDE.Mat d :=
  A z.time z.position z.velocity

@[simp] theorem fullKineticCoefficientAt_apply (z : KineticPoint d) :
    fullKineticCoefficientAt A z = A z.time z.position z.velocity :=
  rfl

section
variable (u : KineticPoint d → ℝ) (z : KineticPoint d)
include u z

/-- The backward kinetic operator with full coefficient dependence. -/
def backwardOperator : ℝ :=
  Parabolic.kineticTimeDerivative u z +
    PDE.vecDot z.velocity (Parabolic.kineticPositionGradient u z) -
      matrixContraction (fullKineticCoefficientAt A z)
        (Parabolic.kineticVelocityHessian u z)

@[simp] theorem backwardOperator_apply :
    backwardOperator A u z =
      Parabolic.kineticTimeDerivative u z +
        PDE.vecDot z.velocity (Parabolic.kineticPositionGradient u z) -
          matrixContraction (fullKineticCoefficientAt A z)
            (Parabolic.kineticVelocityHessian u z) :=
  rfl

end

end

section
variable {d : ℕ} (A : CoefficientField d)
include A

/-- Lift a time--velocity coefficient without introducing position dependence. -/
def ofTimeVelocityCoefficient :
    FullKineticCoefficient d :=
  fun t _x v => A t v

@[simp] theorem ofTimeVelocityCoefficient_apply (t : ℝ) (x v : PDE.Vec d) :
    ofTimeVelocityCoefficient A t x v = A t v :=
  rfl

section
variable (u : KineticPoint d → ℝ) (z : KineticPoint d)
include u z

/-- The backward operator specialized to a coefficient independent of position. -/
def backwardOperatorOfTimeVelocityCoefficient : ℝ :=
  backwardOperator (ofTimeVelocityCoefficient A) u z

@[simp] theorem backwardOperatorOfTimeVelocityCoefficient_apply :
    backwardOperatorOfTimeVelocityCoefficient A u z =
      Parabolic.kineticTimeDerivative u z +
        PDE.vecDot z.velocity (Parabolic.kineticPositionGradient u z) -
          matrixContraction (A z.time z.velocity)
            (Parabolic.kineticVelocityHessian u z) :=
  rfl

end

end

section
variable (a : ℝ → ℝ → ℝ) (u : KineticPoint 1 → ℝ) (z : KineticPoint 1)
include a u z

/-- The autonomous scalar backward operator on the one-dimensional carrier. -/
def autonomousScalarOperator : ℝ :=
  Parabolic.kineticTimeDerivative u z +
    z.velocity 0 * Parabolic.kineticPositionGradient u z 0 -
      a (z.position 0) (z.velocity 0) *
        Parabolic.kineticVelocityHessian u z 0 0

@[simp] theorem autonomousScalarOperator_apply :
    autonomousScalarOperator a u z =
      Parabolic.kineticTimeDerivative u z +
        z.velocity 0 * Parabolic.kineticPositionGradient u z 0 -
          a (z.position 0) (z.velocity 0) *
            Parabolic.kineticVelocityHessian u z 0 0 :=
  rfl

end

section
variable {n : ℕ} (u : KineticPoint n → ℝ) (z : KineticPoint n)
include u z

/-- The Hessian in the diffused `y` coordinate of a transported point. -/
def diffusedHessian : PDE.Mat n :=
  fun i j =>
    (fderiv ℝ (fun y : PDE.Vec n =>
      Parabolic.kineticPositionGradient u ⟨z.time, y, z.velocity⟩)
      z.position (PDE.basisVec i)) j

@[simp] theorem diffusedHessian_apply (i j : Fin n) :
    diffusedHessian u z i j =
      (fderiv ℝ (fun y : PDE.Vec n =>
        Parabolic.kineticPositionGradient u ⟨z.time, y, z.velocity⟩)
        z.position (PDE.basisVec i)) j :=
  rfl

end

section
variable {n : ℕ} (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) (u : KineticPoint n → ℝ)
  (z : KineticPoint n)
include n B b u z

/-- The forward operator with diffusion in `y` and transport in `z`. -/
def transportedForwardOperator : ℝ :=
  Parabolic.kineticTimeDerivative u z +
    matrixContraction (fullKineticCoefficientAt B z) (diffusedHessian u z) +
      PDE.vecDot (b z.position) (Parabolic.kineticVelocityGradient u z)

@[simp] theorem transportedForwardOperator_apply :
    transportedForwardOperator B b u z =
      Parabolic.kineticTimeDerivative u z +
        matrixContraction (fullKineticCoefficientAt B z) (diffusedHessian u z) +
          PDE.vecDot (b z.position) (Parabolic.kineticVelocityGradient u z) :=
  rfl

end

section
variable {n : ℕ} (B : CoefficientField n)
include B

/-- Lift a coefficient independent of the transported `z` coordinate. -/
def zIndependentCoefficient :
    FullKineticCoefficient n :=
  fun sigma y _z => B sigma y

@[simp] theorem zIndependentCoefficient_apply (sigma : ℝ) (y z : PDE.Vec n) :
    zIndependentCoefficient B sigma y z = B sigma y :=
  rfl

section
variable (b : PDE.Vec n → PDE.Vec n) (u : KineticPoint n → ℝ) (z : KineticPoint n)
include b u z

/-- The transported operator specialized to a z-independent coefficient. -/
def transportedForwardOperatorOfTimeDiffusedCoefficient : ℝ :=
  transportedForwardOperator (zIndependentCoefficient B) b u z

@[simp] theorem transportedForwardOperatorOfTimeDiffusedCoefficient_apply :
    transportedForwardOperatorOfTimeDiffusedCoefficient B b u z =
      Parabolic.kineticTimeDerivative u z +
        matrixContraction (B z.time z.position) (diffusedHessian u z) +
          PDE.vecDot (b z.position) (Parabolic.kineticVelocityGradient u z) :=
  rfl

end

end

end HypoellipticAleksandrov.KineticAleksandrov
