module

import HypoellipticAleksandrov.KineticAleksandrov.Decay.ScalarTerminalComparison

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceCanonical
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrinciple
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus

/-! # Scalar terminal comparison on a velocity ball

The comparison lemma is an internal maximum-principle tool for the exponential
short-time barrier. Continuity passes the initial time face.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- A smooth subsolution lies below the supplied scalar terminal solution on a ball. -/
theorem ball_terminal_lower_comparison {d : ℕ} {lam Lam σ τ R : ℝ}
    (v₀ : PDE.Vec d) (hR : 0 < R) (hστ : σ < τ) (hlam : 0 < lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (F : BoundedBorel (PDE.Vec d)) (V U : TimeVelocity d → ℝ)
    (hV : ParabolicProbe.IsClassicalScalarTerminalSolution (PDE.euclideanBall v₀ R)
      stationary (zIndependentCoefficient B) τ F V)
    (hUc : ContinuousOn U (scalarParabolicClosedCylinder σ τ
      (PDE.euclideanBall v₀ R)))
    (hUj : ∀ p ∈ scalarParabolicOpenCylinder σ τ (PDE.euclideanBall v₀ R),
      ContDiffAt ℝ 2 U p)
    (hUs : ∀ p ∈ scalarParabolicOpenCylinder σ τ (PDE.euclideanBall v₀ R),
      0 ≤ scalarParabolicOperator B 0 U p)
    (hterm : ∀ v ∈ closure (PDE.euclideanBall v₀ R), U (τ, v) ≤ F v)
    (hlat : ∀ p ∈ scalarParabolicLateralFace σ τ (PDE.euclideanBall v₀ R),
      U p ≤ 0) :
    ∀ v ∈ closure (PDE.euclideanBall v₀ R), U (σ, v) ≤ V (σ, v) := by
  have h := scalar_terminal_signed_comparison (Or.inl ⟨v₀, R, hR, rfl⟩)
    hστ B (fun t v => (posDef_of_loewner_lower hlam (hB.2.2.2.2.1 t v)).posSemidef)
    F hV hUc hUj 1
    (fun p hp => by simpa only [one_mul] using hUs p hp)
    (fun v hv => by simpa only [one_mul, sub_nonpos] using hterm v hv)
    (fun p hp => by simpa only [one_mul] using hlat p hp)
  simpa only [one_mul, sub_nonpos] using h

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
