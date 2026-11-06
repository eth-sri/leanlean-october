module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Setting
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ReflectionCalculus

/-! # Scalar/full operator and autonomous reflection identities -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov.Parabolic

variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (a : ℝ → ℝ → ℝ) (u : Point → ℝ) (p : Point)

/-- The full backward operator is the autonomous scalar operator in dimension one. -/
theorem backwardOperator_autonomous  :
    backwardOperator (autonomousCoefficient a) u p = autonomousScalarOperator a u p := by
  simp only [backwardOperator, autonomousScalarOperator, autonomousCoefficient,
    fullKineticCoefficientAt, matrixContraction, PDE.vecDot, Fin.sum_univ_one]

/-- The full forward operator agrees with the scalar forward evaluator. -/
theorem forwardOperator_autonomous  :
    forwardKineticOperator (autonomousCoefficient a) u p = forwardScalarOperator a u p := by
  simp only [forwardKineticOperator, forwardScalarOperator, autonomousCoefficient,
    fullKineticCoefficientAt, matrixContraction, PDE.vecDot, Fin.sum_univ_one]

/-- The source reflection converts the autonomous backward equation to its forward equation. -/
theorem autonomousScalarOperator_reflection  :
    forwardScalarOperator (reflectedAutonomous a) (u ∘ kineticReflection) p =
      -autonomousScalarOperator a u (kineticReflection p) := by
  rw [forwardScalarOperator, autonomousScalarOperator, kineticTimeDerivative_reflection,
    kineticPositionGradient_reflection, kineticVelocityHessian_reflection]
  simp only [reflectedAutonomous, kineticReflection, Pi.neg_apply]
  ring

/-- Reflection preserves the scalar pointwise coefficient bounds. -/
theorem reflectedAutonomous_bounds  :
    ∀ x v, lam ≤ reflectedAutonomous A.a x v ∧ reflectedAutonomous A.a x v ≤ Lam := by
  intro x v
  exact A.bounds _ v

/-- Reflection preserves genuine C-infinity smoothness of the scalar coefficient. -/
theorem reflectedAutonomous_smooth  :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (reflectedAutonomous A.a)) := A.smooth.comp (contDiff_fst.neg.prodMk contDiff_snd)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
