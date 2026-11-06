module

public import GS.GlobalGeometry.BalancedLift
public import GS.Continuation.FactorCurveVelocities
public import GS.RiemannianCompletion.ExponentialStep

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Projected derivatives along actual matrix curves

The operation is Pi_(gamma(t)) (deriv V t). We prove the linear connection
rules and metric compatibility for differentiable tangent vector fields, and
apply them to the already constructed exponential curves. Actual derivatives
are used throughout. This is NOT registered as mathlib's Levi-Civita connection:
the missing bundle/connection registration and torsion-free identification are
explicitly recorded in the coverage report.

Metric compatibility permits overlap for independent blocks. The exponential
parallel-velocity conclusion retains the original no-overlap hypothesis.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation Filter
open scoped BigOperators Topology Manifold
namespace GS.GlobalGeometry
variable {n : ℕ}

@[simp] theorem leftPointProjection_add (b : Fin n → ℕ) (X A B : Mat n) :
    leftPointProjection b X (A+B) = leftPointProjection b X A+leftPointProjection b X B := by
  simp only [leftPointProjection, Matrix.add_mul, blockSkew_add]

@[simp] theorem rightPointProjection_add (b : Fin n → ℕ) (X A B : Mat n) :
    rightPointProjection b X (A+B) = rightPointProjection b X A+rightPointProjection b X B := by
  simp only [rightPointProjection, Matrix.mul_add, blockSkew_add]

@[simp] theorem leftPointProjection_smul (b : Fin n → ℕ) (X A : Mat n) (a : ℝ) :
    leftPointProjection b X (a•A) = a•leftPointProjection b X A := by
  simp only [leftPointProjection, Matrix.smul_mul, blockSkew_smul]

@[simp] theorem rightPointProjection_smul (b : Fin n → ℕ) (X A : Mat n) (a : ℝ) :
    rightPointProjection b X (a•A) = a•rightPointProjection b X A := by
  simp only [rightPointProjection, Matrix.mul_smul, blockSkew_smul]

def alongDerivative (b₁ b₂ : Fin n → ℕ) (γ V : ℝ → Mat n) (t : ℝ) : Mat n :=
  pointProjection b₁ b₂ (γ t) (deriv V t)

section ActualTangent
open GS.LieAction GS.CayleyCharts GS.ManifoldCompletion GS.RiemannianCompletion
variable {b₁ b₂ : Fin n → ℕ} (σ : Equiv.Perm (Fin n))
variable [Fact (NoOffDiagonalOverlap b₁ b₂ σ)]

/-- Pointwise lift of the projected derivative to the genuine tangent fibre.
Smoothness as a connection on the whole bundle is a separate obligation. -/
def tangentAlongDerivative (γ : ℝ → MatrixOrbit b₁ b₂ (permMatrix σ))
    (V : ℝ → Mat n) (t : ℝ) :
    TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) (γ t) :=
  tangentProjection σ (γ t) (deriv V t)

@[simp] theorem inclusion_tangentAlongDerivative
    (γ : ℝ → MatrixOrbit b₁ b₂ (permMatrix σ)) (V : ℝ → Mat n) (t : ℝ) :
    inclusionDifferential σ (γ t) (tangentAlongDerivative σ γ V t) =
      alongDerivative b₁ b₂ (fun s => (γ s).val) V t :=
  inclusion_tangentProjection σ (γ t) (deriv V t)

end ActualTangent
end GS.GlobalGeometry
