module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureProbability
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Exact kinetic calculus of the two exponential early-face barriers -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

/-- An exponential plane depending only on time and physical velocity. -/
def reconstructionExponentialPlane (alpha beta gamma : ℝ) (p : Point) : ℝ :=
  Real.exp (alpha * p.time + beta * p.velocity 0 + gamma)

/-- The exponential plane is smooth in the prescribed packed physical coordinates. -/
theorem reconstructionExponentialPlane_smooth (alpha beta gamma : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (reconstructionExponentialPlane alpha beta gamma ∘ reconstructionPhysicalHomeomorph) := by
  have ht : ContDiff ℝ (⊤ : ℕ∞) (Evolution.timeCoord 1) :=
    (Evolution.timeCoord 1).contDiff
  exact ((contDiff_const.mul ht).add
    (contDiff_const.mul ((contDiff_apply ℝ ℝ _).comp
      (diffusedCoord 1).contDiff)) |>.add contDiff_const).exp

private theorem exponentialPlane_second_deriv (c beta : ℝ) (v : ℝ) :
    deriv (deriv (fun w => Real.exp (c + beta * w))) v =
      beta ^ 2 * Real.exp (c + beta * v) := by
  have hd (w : ℝ) : HasDerivAt (fun w => Real.exp (c + beta * w))
      (Real.exp (c + beta * w) * beta) w :=
    by simpa using
      (((hasDerivAt_id w).const_mul beta).const_add c).exp
  have heq : deriv _ =
      fun w => Real.exp (c + beta * w) * beta := funext (fun w => (hd w).deriv)
  rw [heq, (hd v |>.mul_const beta).deriv]
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
        _).add_const gamma).exp.deriv
  have hx : kineticPositionGradient (reconstructionExponentialPlane alpha beta gamma) p 0 = 0 := by
    rw [kineticPositionGradient_scalar]
    change deriv (fun _ : ℝ => Real.exp (alpha * p.time + beta * p.velocity 0 + gamma))
      _ = 0
    simp
  have hv : kineticVelocityHessian (reconstructionExponentialPlane alpha beta gamma) p 0 0 =
      beta ^ 2 * reconstructionExponentialPlane alpha beta gamma p := by
    rw [kineticVelocityHessian_scalar]
    have heq : (fun v => reconstructionExponentialPlane alpha beta gamma
        ⟨p.time, p.position, fun _ => v⟩) =
        fun v => Real.exp ((alpha * p.time + gamma) + beta * v) := by
      dsimp only [reconstructionExponentialPlane]
      ring
    rw [heq, exponentialPlane_second_deriv]
    dsimp only [reconstructionExponentialPlane]
    ring
  unfold forwardScalarOperator
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
