module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Setting
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ReflectionCalculus
public import PDEFoundation.Calculus.RegularityOrder


/-! # Scalar/full operator and autonomous reflection identities -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous


variable (a : ℝ → ℝ → ℝ) (u : Point → ℝ) (p : Point)

/-- The full backward operator is the autonomous scalar operator in dimension one. -/
theorem backwardOperator_autonomous  :
    backwardOperator (autonomousCoefficient a) u p = autonomousScalarOperator a u p := by
  simp_all [backwardOperator, autonomousScalarOperator, autonomousCoefficient, fullKineticCoefficientAt, matrixContraction, PDE.vecDot]

/-- The full forward operator agrees with the scalar forward evaluator. -/
theorem forwardOperator_autonomous  :
    forwardKineticOperator (autonomousCoefficient a) u p = forwardScalarOperator a u p := by
  simp_all [forwardKineticOperator, forwardScalarOperator, autonomousCoefficient, fullKineticCoefficientAt, matrixContraction, PDE.vecDot]

/-- The source reflection converts the autonomous backward equation to its forward equation. -/
theorem autonomousScalarOperator_reflection  :
    forwardScalarOperator (reflectedAutonomous a) (u ∘ kineticReflection) p =
      -autonomousScalarOperator a u (kineticReflection p) := by
  rw [forwardScalarOperator, autonomousScalarOperator, kineticTimeDerivative_reflection,
    kineticPositionGradient_reflection, kineticVelocityHessian_reflection]
  simp only [reflectedAutonomous, kineticReflection, Pi.neg_apply]
  ring

variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)

/-- Reflection preserves the scalar pointwise coefficient bounds. -/
theorem reflectedAutonomous_bounds  :
    ∀ x v, lam ≤ reflectedAutonomous A.a x v ∧ reflectedAutonomous A.a x v ≤ Lam := (fun x => A.bounds (-x))

/-- Reflection preserves genuine C-infinity smoothness of the scalar coefficient. -/
theorem reflectedAutonomous_smooth  :
    ContDiff ℝ PDE.smoothOrder (Function.uncurry (reflectedAutonomous A.a)) := A.smooth.comp (contDiff_fst.neg.prodMk contDiff_snd)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
