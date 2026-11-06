module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CapacityTest
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdaptersCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! # Velocity-only tests and their strip bounds -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic

/-- The forward operator on a velocity-only test has only its diffusion term. -/
theorem capacity_velocity_operator (a : ℝ → ℝ → ℝ) (Phi : ℝ → ℝ) (p : Point) :
    forwardScalarOperator a (fun q => Phi (q.velocity 0)) p =
      a (p.position 0) (p.velocity 0) * deriv (deriv Phi) (p.velocity 0) := by
  rw [forwardScalarOperator, kineticPositionGradient_scalar, kineticVelocityHessian_scalar]
  simp only [kineticTimeDerivative, deriv_const, mul_zero, zero_add]

variable {Phi : ℝ → ℝ}

/-- Raw physical smoothness of a smooth velocity-only test. -/
theorem capacity_velocity_smooth  (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) :
    ContDiff ℝ (⊤ : ℕ∞)
      ((fun q : Point => Phi (q.velocity 0)) ∘ (KineticPoint.equivProd 1).symm) :=
  hPhi.comp ((contDiff_apply ℝ ℝ _).comp contDiff_snd.snd)

/-- A derivative bound controls differences of the convex test on the closed strip. -/
theorem capacity_test_difference  (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    {D : ℝ} (hD : 0 ≤ D) (hd : ∀ v, |deriv Phi v| ≤ D)
    (H : Interval) {x y : ℝ} (hx : x ∈ Icc H.lo H.hi) (hy : y ∈ Icc H.lo H.hi) :
    |Phi y - Phi x| ≤ D * (H.hi - H.lo) := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun v (_) => hPhi.differentiable (by norm_num) v)
    (fun v (_) => by simpa only [Real.norm_eq_abs] using hd v)
    convex_univ (mem_univ x) (mem_univ y)
  have hb : |y - x| ≤ H.hi - H.lo := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  simpa only [Real.norm_eq_abs] using h.trans (mul_le_mul_of_nonneg_left hb hD)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
