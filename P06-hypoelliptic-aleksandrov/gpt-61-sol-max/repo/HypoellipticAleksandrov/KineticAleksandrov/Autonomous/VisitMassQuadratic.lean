module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CapacityCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic
public import PDEFoundation.Calculus.RegularityOrder


/-! # The source quadratic test for counting entrances -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set

variable (c : Clock)

variable (v : ℝ)

/-- The quadratic test vanishing at the active interval's endpoints. -/
def visitQuadratic   : ℝ :=
  (v - (c.vbar - 3 * c.r / 4)) * (c.vbar + 3 * c.r / 4 - v)

/-- Centered form of the visit-counting quadratic. -/
theorem visitQuadratic_centered   :
    visitQuadratic c v = 9 * c.r ^ 2 / 16 - (v - c.vbar) ^ 2 := by
  unfold visitQuadratic
  ring

/-- Smoothness of the quadratic test. -/
theorem visitQuadratic_smooth  : ContDiff ℝ PDE.smoothOrder (visitQuadratic c) :=
  (contDiff_id.sub contDiff_const).mul (contDiff_const.sub contDiff_id)

/-- First derivative of the source quadratic. -/
theorem visitQuadratic_deriv  :
    deriv (visitQuadratic c) = fun v => -2 * (v - c.vbar) := by
  funext v
  have hd := ((hasDerivAt_id v).sub_const (c.vbar - 3 * c.r / 4)).mul
    ((hasDerivAt_const v (c.vbar + 3 * c.r / 4)).sub (hasDerivAt_id v))
  change HasDerivAt (visitQuadratic c) _ v at hd
  rw [hd.deriv]
  simp only [Pi.sub_apply, id_eq, one_mul]
  ring

/-- The second derivative is the constant minus two. -/
theorem visitQuadratic_second  (v : ℝ) :
    deriv (deriv (visitQuadratic c)) v = -2 := by
  simp_all [visitQuadratic_deriv]

/-- The forward operator of the velocity quadratic equals minus twice the coefficient. -/
theorem visitQuadratic_operator  (a : ℝ → ℝ → ℝ) (p : Point) :
    forwardScalarOperator a (fun q => visitQuadratic c (q.velocity 0)) p =
      -2 * a (p.position 0) (p.velocity 0) := by
  rw [capacity_velocity_operator, visitQuadratic_second]
  ring

/-- The test is bounded above by its central maximum on every velocity. -/
theorem visitQuadratic_le  (v : ℝ) :
    visitQuadratic c v ≤ 9 * c.r ^ 2 / 16 := by
  rw [visitQuadratic_centered]
  exact sub_le_self _ (sq_nonneg _)

variable {v : ℝ}

/-- Nonnegativity on the closed active interval. -/
theorem visitQuadratic_nonneg   (hv : v ∈ closure c.active) :
    0 ≤ visitQuadratic c v := by
  have ho : c.vbar - 3 * c.r / 4 < c.vbar + 3 * c.r / 4 := by
    linarith [c.positive]
  rw [Clock.active, closure_Ioo ho.ne] at hv
  exact mul_nonneg (sub_nonneg.mpr hv.1) (sub_nonneg.mpr hv.2)

/-- The exact lower bound on the closed entrance interval. -/
theorem visitQuadratic_entrance_lower
    (hv : v ∈ closure c.entrance) : 5 * c.r ^ 2 / 16 ≤ visitQuadratic c v := by
  have ho : c.vbar - c.r / 2 < c.vbar + c.r / 2 := by linarith [c.positive]
  rw [Clock.entrance, closure_Ioo ho.ne] at hv
  rw [visitQuadratic_centered]
  have hp : 0 ≤ (v - c.vbar + c.r / 2) * (c.r / 2 - (v - c.vbar)) :=
    mul_nonneg (by linarith [hv.1]) (by linarith [hv.2])
  nlinarith only [hp]

/-- Vanishing at both active endpoints. -/
theorem visitQuadratic_endpoints  :
    visitQuadratic c (c.vbar - 3 * c.r / 4) = 0 ∧
      visitQuadratic c (c.vbar + 3 * c.r / 4) = 0 := by
  simp_all [visitQuadratic]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
