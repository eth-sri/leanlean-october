module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationParametersPositive
import Mathlib.Tactic

/-! # Radius containment and joint source propagation parameter bounds -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

/-- The source velocity step restriction gives the half-radius containment bound. -/
theorem propagation_step_velocity {d : ℕ} {lam Lam H T0 T1 kx kv h : ℝ}
    (hH : 0 ≤ H) (hkv : 0 < kv) (_hh : 0 < h)
    (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) :
    velocityTubeConstant d lam Lam H T1 * Real.sqrt h ≤ kv / 2 := by
  have hc := (tubeConstants_pos (d := d) (lam := lam) (Lam := Lam) (T1 := T1) hH).1
  have hratio : 0 < kv / (2 * velocityTubeConstant d lam Lam H T1) := by positivity
  have hb := Real.sqrt_le_sqrt
    (hhstar.trans (stepSize_le_velocity d lam Lam H T0 T1 kx kv))
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hratio] at hb
  calc
    _ ≤ velocityTubeConstant d lam Lam H T1 *
        (kv / (2 * velocityTubeConstant d lam Lam H T1)) :=
      mul_le_mul_of_nonneg_left hb hc.le
    _ = _ := by field_simp

/-- The source position step restriction gives the half-radius containment bound. -/
theorem propagation_step_position {d : ℕ} {lam Lam H T0 T1 kx kv h : ℝ}
    (hH : 0 ≤ H) (hkx : 0 < kx) (hh : 0 < h)
    (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) :
    positionTubeConstant d lam Lam H T1 * h ^ (3 / 2 : ℝ) ≤ kx / 2 := by
  have hc := (tubeConstants_pos (d := d) (lam := lam) (Lam := Lam) (T1 := T1) hH).2
  have hratio : 0 < kx / (2 * positionTubeConstant d lam Lam H T1) := by positivity
  have hb := Real.rpow_le_rpow hh.le
    (hhstar.trans (stepSize_le_position d lam Lam H T0 T1 kx kv))
    (show (0 : ℝ) ≤ 3 / 2 by norm_num)
  rw [← Real.rpow_mul hratio.le] at hb
  norm_num at hb
  calc
    _ ≤ positionTubeConstant d lam Lam H T1 *
        (kx / (2 * positionTubeConstant d lam Lam H T1)) :=
      mul_le_mul_of_nonneg_left hb hc.le
    _ = _ := by field_simp

end HypoellipticAleksandrov.KineticAleksandrov.Holder
