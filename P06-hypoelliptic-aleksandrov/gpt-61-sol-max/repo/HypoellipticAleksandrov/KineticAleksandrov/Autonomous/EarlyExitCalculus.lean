module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureProbability
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import PDEFoundation.Calculus.RegularityOrder


/-! # Exact kinetic calculus of the two exponential early-face barriers -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic
open Evolution

variable (alpha beta gamma : ℝ)

/-- An exponential plane depending only on time and physical velocity. -/
def reconstructionExponentialPlane  (p : Point) : ℝ :=
  Real.exp (alpha * p.time + beta * p.velocity 0 + gamma)

/-- The exponential plane is smooth in the prescribed packed physical coordinates. -/
theorem reconstructionExponentialPlane_smooth  :
    ContDiff ℝ PDE.smoothOrder
      (reconstructionExponentialPlane alpha beta gamma ∘ reconstructionPhysicalHomeomorph) := (id
  (ContDiff.exp
    (ContDiff.add
      (ContDiff.add (ContDiff.mul contDiff_const (ContinuousLinearMap.contDiff (Evolution.timeCoord 1)))
        (ContDiff.mul contDiff_const
          (ContDiff.comp (contDiff_apply ℝ ℝ 0) (ContinuousLinearMap.contDiff (diffusedCoord 1)))))
      contDiff_const)))

private theorem exponentialPlane_second_deriv (c beta : ℝ) (v : ℝ) :
    deriv (deriv (fun w => Real.exp (c + beta * w))) v =
      beta ^ 2 * Real.exp (c + beta * v) := by
  have hd (w : ℝ) : HasDerivAt (fun w => Real.exp (c + beta * w))
      (Real.exp (c + beta * w) * beta) w :=
    by simpa only [id_eq, mul_one] using
      (((hasDerivAt_id w).const_mul beta).const_add c).exp

  rw [(funext (fun w => (hd w).deriv)), (hd v |>.mul_const beta).deriv]
  ring

/-- No coefficient derivative occurs in the exponential plane operator. -/
theorem reconstructionExponentialPlane_operator (a : ℝ → ℝ → ℝ)
    (alpha beta gamma : ℝ) (p : Point) :
    forwardScalarOperator a (reconstructionExponentialPlane alpha beta gamma) p =
      (alpha + a (p.position 0) (p.velocity 0) * beta ^ 2) *
        reconstructionExponentialPlane alpha beta gamma p := by
  have ht : kineticTimeDerivative (reconstructionExponentialPlane alpha beta gamma) p =
      alpha * reconstructionExponentialPlane alpha beta gamma p := by
    change deriv (fun t => Real.exp (alpha * t + beta * p.velocity 0 + gamma)) p.time = _
    simpa only [id_eq, mul_one, reconstructionExponentialPlane, mul_comm] using
      ((((hasDerivAt_id p.time).const_mul alpha).add_const
        (beta * p.velocity 0)).add_const gamma).exp.deriv
  have hx : kineticPositionGradient (reconstructionExponentialPlane alpha beta gamma) p 0 = 0 := by
    rw [kineticPositionGradient_scalar]
    change deriv (fun _ : ℝ => Real.exp (alpha * p.time + beta * p.velocity 0 + gamma))
      (p.position 0) = 0
    exact deriv_const _ _
  have hv : kineticVelocityHessian (reconstructionExponentialPlane alpha beta gamma) p 0 0 =
      beta ^ 2 * reconstructionExponentialPlane alpha beta gamma p := by
    rw [kineticVelocityHessian_scalar]
    have heq : (fun v => reconstructionExponentialPlane alpha beta gamma
        ⟨p.time, p.position, fun _ => v⟩) =
        fun v => Real.exp ((alpha * p.time + gamma) + beta * v) := by
      funext v
      dsimp only [reconstructionExponentialPlane]
      congr 1
      ring
    rw [heq, exponentialPlane_second_deriv]
    dsimp only [reconstructionExponentialPlane]
    congr 2
    ring
  unfold forwardScalarOperator
  rw [ht, hx, hv]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
