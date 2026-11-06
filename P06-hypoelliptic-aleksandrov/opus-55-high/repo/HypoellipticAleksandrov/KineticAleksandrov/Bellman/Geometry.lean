module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.ExponentSetting
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Literal plane geometry for the homogeneous Bellman problem -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The anisotropic position-velocity dilation on the ambient plane. -/
def bellmanPlaneDilation (r : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (r ^ 3 * q.1, r * q.2)

/-- The polynomial whose sixth root is the source gauge. -/
def bellmanGaugePower (q : ℝ × ℝ) : ℝ := q.1 ^ 2 + q.2 ^ 6

/-- The source gauge, with homogeneous dimension four. -/
def bellmanGauge (q : ℝ × ℝ) : ℝ := bellmanGaugePower q ^ (1 / 6 : ℝ)

variable (r : ℝ) (q : ℝ × ℝ)

/-- The gauge polynomial is nonnegative. -/
theorem bellmanGaugePower_nonneg  : 0 ≤ bellmanGaugePower q := add_nonneg (sq_nonneg q.1) (Even.pow_nonneg (by decide) q.2)

/-- The gauge polynomial vanishes precisely at the origin. -/
theorem bellmanGaugePower_eq_zero_iff  :
    bellmanGaugePower q = 0 ↔ q = (0, 0) := by
  constructor
  · intro h
    change q.1 ^ 2 + q.2 ^ 6 = 0 at h
    have hx : q.1 ^ 2 = 0 := le_antisymm
      (by nlinarith only [h, Even.pow_nonneg (by decide : Even 6) q.2]) (sq_nonneg q.1)
    aesop
  · rintro rfl
    norm_num [bellmanGaugePower]

/-- The gauge polynomial scales with degree six. -/
theorem bellmanGaugePower_dilation  :
    bellmanGaugePower (bellmanPlaneDilation r q) = r ^ 6 * bellmanGaugePower q := by
  dsimp [bellmanGaugePower, bellmanPlaneDilation]
  ring

/-- The gauge has degree one under positive kinetic dilation. -/
theorem bellmanGauge_dilation  (hr : 0 < r) (q : ℝ × ℝ) :
    bellmanGauge (bellmanPlaneDilation r q) = r * bellmanGauge q := by
  rw [bellmanGauge, bellmanGaugePower_dilation,
    Real.mul_rpow (pow_nonneg hr.le 6) (bellmanGaugePower_nonneg q)]
  have h : (r ^ 6) ^ (1 / 6 : ℝ) = r := by
    convert Real.pow_rpow_inv_natCast hr.le (by decide : (6) ≠ 0) using 1
    norm_num
  rw [h]
  rfl

/-- Positive dilation preserves the punctured plane. -/
theorem bellmanPlaneDilation_ne_zero  (hr : 0 < r) (q : ℝ × ℝ)
    (hq : q ≠ (0, 0)) : bellmanPlaneDilation r q ≠ (0, 0) := by
  intro h
  apply hq
  have hx : r ^ 3 * q.1 = 0 := congrArg Prod.fst h
  have hv : r * q.2 = 0 := congrArg Prod.snd h
  aesop

/-- Ambient and punctured dilation are the same literal map. -/
theorem bellmanDilation_val  (hr : 0 < r) (q : BellmanPuncturedPlane) :
    (bellmanDilation r hr q).val = bellmanPlaneDilation r q.val := rfl

/-- Kinetic dilations compose multiplicatively. -/
theorem bellmanPlaneDilation_comp (r s : ℝ) (q : ℝ × ℝ) :
    bellmanPlaneDilation r (bellmanPlaneDilation s q) = bellmanPlaneDilation (r * s) q := by
  apply Prod.ext <;> dsimp [bellmanPlaneDilation] <;> ring

end HypoellipticAleksandrov.KineticAleksandrov
