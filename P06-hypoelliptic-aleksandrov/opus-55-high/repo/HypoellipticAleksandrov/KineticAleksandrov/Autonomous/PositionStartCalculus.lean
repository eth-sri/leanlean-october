module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassOutgoing
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartTest
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! # The position-localized quadratic visit test -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set

variable (c : Clock)

/-- The position-localized quadratic has exactly the source transport-diffusion operator. -/
theorem positionStartQuadratic_operator  (eta : ℝ → ℝ)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (a : ℝ → ℝ → ℝ) (p : Point) :
    forwardScalarOperator a (fun q => eta (q.position 0) * visitQuadratic c (q.velocity 0)) p =
      p.velocity 0 * deriv eta (p.position 0) * visitQuadratic c (p.velocity 0) -
        2 * a (p.position 0) (p.velocity 0) * eta (p.position 0) := by
  have hposition : deriv (fun X => eta X * visitQuadratic c _)
      _ = deriv eta _ * visitQuadratic c (p.velocity 0) :=
    ((heta.differentiable (by norm_num) (p.position 0)).hasDerivAt.mul_const _).deriv
  have hquad (v : ℝ) : HasDerivAt (visitQuadratic c) (-2 * (v - c.vbar)) v := by
    have h := ((visitQuadratic_smooth c).differentiable (by norm_num) v).hasDerivAt
    rwa [visitQuadratic_deriv] at h
  have hfirst : deriv (fun v => eta _ * visitQuadratic c v) =
      fun v => eta _ * (-2 * (v - c.vbar)) :=
    funext fun v => ((hquad v).const_mul (eta (p.position 0))).deriv
  have hsecond : deriv (deriv (fun v => eta (p.position 0) * visitQuadratic c v)) (p.velocity 0) =
      eta (p.position 0) * (-2) := by
    simp_all
  rw [forwardScalarOperator, kineticPositionGradient_scalar, kineticVelocityHessian_scalar]
  simp only [kineticTimeDerivative, deriv_const, hposition, hsecond]
  ring

/-- New starts in the chosen position cell retain the exact `5*r²/16` weight. -/
theorem positionStartQuadratic_start_lower  (x : ℝ) (k : ℤ) (p : Point)
    (hx : p.position 0 ∈ enlargedPositionCell c.r x k)
    (hv : p.velocity 0 ∈ closure c.entrance) :
    5 * c.r ^ 2 / 16 ≤
      positionStartCutoff (x + ((k : ℝ) + 1 / 2) * c.r ^ 3) c.r c.positive
        (p.position 0) * visitQuadratic c (p.velocity 0) := by
  rw [positionStartCutoff_eq_one_on_cell c.r x c.positive k hx, one_mul]
  exact visitQuadratic_entrance_lower c hv

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
