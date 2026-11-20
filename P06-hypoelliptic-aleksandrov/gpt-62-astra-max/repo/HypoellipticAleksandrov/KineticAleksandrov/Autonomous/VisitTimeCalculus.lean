module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassQuadratic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitTimeCutoff
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! # The genuine time-localized quadratic visit test -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic

variable (c : Clock) (eta : ℝ → ℝ) (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
include heta

/-- The time-localized quadratic has exactly the source transport-diffusion operator. -/
theorem visitTimeQuadratic_operator (a : ℝ → ℝ → ℝ) (p : Point) :
    forwardScalarOperator a (fun q => eta q.time * visitQuadratic c (q.velocity 0)) p =
      deriv eta p.time * visitQuadratic c (p.velocity 0) -
        2 * a (p.position 0) (p.velocity 0) * eta p.time := by
  have hquad (v : ℝ) : HasDerivAt (visitQuadratic c) (-2 * (v - c.vbar)) v := by
    have h := ((visitQuadratic_smooth c).differentiable (by norm_num) v).hasDerivAt
    rwa [visitQuadratic_deriv] at h
  have hsecond : deriv (deriv (fun v => eta p.time * visitQuadratic c v)) (p.velocity 0) =
      eta p.time * (-2) := by
    rw [(funext fun v => ((hquad v).const_mul (eta p.time)).deriv)]
    simp
  rw [forwardScalarOperator, kineticPositionGradient_scalar, kineticVelocityHessian_scalar]
  simp_all [kineticTimeDerivative] <;> linarith

/-- Raw physical smoothness of the time-localized quadratic. -/
theorem visitTimeQuadratic_smooth :
    ContDiff ℝ (⊤ : ℕ∞)
      ((fun q : Point => eta q.time * visitQuadratic c (q.velocity 0)) ∘
        (KineticPoint.equivProd 1).symm) :=
  (heta.comp contDiff_fst).mul (capacity_velocity_smooth (visitQuadratic_smooth c))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
