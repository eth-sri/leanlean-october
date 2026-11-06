module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.ExponentSetting
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Literal plane geometry for the homogeneous Bellman problem -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov

/- The anisotropic position-velocity dilation on the ambient plane. -/
def bellmanPlaneDilation (r : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (r ^ 3 * q.1, r * q.2)

/- The polynomial whose sixth root is the source gauge. -/
def bellmanGaugePower (q : ℝ × ℝ) : ℝ := q.1 ^ 2 + q.2 ^ 6

/- The source gauge, with homogeneous dimension four. -/
def bellmanGauge (q : ℝ × ℝ) : ℝ := bellmanGaugePower q ^ (1 / 6 : ℝ)

/- The gauge polynomial is nonnegative. -/
theorem bellmanGaugePower_nonneg (q : ℝ × ℝ) : 0 ≤ bellmanGaugePower q :=  add_nonneg (sq_nonneg q.1) (Even.pow_nonneg (by decide : Even 6) q.2)

/- The gauge polynomial vanishes precisely at the origin. -/
theorem bellmanGauge_dilation (r : ℝ) (hr : 0 < r) (q : ℝ × ℝ) :
    bellmanGauge (bellmanPlaneDilation r q) = r * bellmanGauge q := by
  have _h_inl_12 (r : ℝ) (q) : bellmanGaugePower (bellmanPlaneDilation r q) = r ^ 6 * bellmanGaugePower q := by
    dsimp [bellmanGaugePower, bellmanPlaneDilation]
    ring
  rw [bellmanGauge, _h_inl_12,
    Real.mul_rpow (pow_nonneg hr.le 6) (bellmanGaugePower_nonneg q)]
  have h : (r ^ 6) ^ (1 / 6 : ℝ) = r := by
    convert Real.pow_rpow_inv_natCast hr.le (by decide : (6 : ℕ) ≠ 0) using 1
    norm_num
  rw [h]
  rfl

/- Positive dilation preserves the punctured plane. -/
theorem bellmanPlaneDilation_ne_zero (r : ℝ) (hr : 0 < r) (q )
    (hq : q ≠ (0, 0)) : bellmanPlaneDilation r q ≠ (0, 0) := by
  intro h
  apply hq
  have hx := congrArg Prod.fst h
  have hv := congrArg Prod.snd h
  exact Prod.ext ((mul_eq_zero.mp hx).resolve_left (pow_ne_zero 3 hr.ne'))
    ((mul_eq_zero.mp hv).resolve_left hr.ne')

theorem bellmanDilation_val (r : ℝ) (hr : 0 < r) (q : BellmanPuncturedPlane) :
    (bellmanDilation r hr q).val = bellmanPlaneDilation r q.val := rfl

theorem bellmanPlaneDilation_comp (r s : ℝ) (q : ℝ × ℝ) :
    bellmanPlaneDilation r (bellmanPlaneDilation s q) = bellmanPlaneDilation (r * s) q := by
  apply Prod.ext <;> dsimp [bellmanPlaneDilation] <;> ring

end HypoellipticAleksandrov.KineticAleksandrov
