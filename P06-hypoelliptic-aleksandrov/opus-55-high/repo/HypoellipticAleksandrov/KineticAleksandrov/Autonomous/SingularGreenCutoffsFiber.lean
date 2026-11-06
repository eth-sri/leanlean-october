module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsModulus

/-! # Position-fiber majorants of the actual homogeneous Bellman jets -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory

/-- The position coordinate gives its own cube-root gauge lower bound. -/
theorem barrier_position_gauge_lower (q : ℝ × ℝ) : |q.1| ^ (1 / 3 : ℝ) ≤ bellmanGauge q := by
  have hh := Real.rpow_le_rpow (abs_nonneg q.1) (bellmanGauge_coordinate_bounds q).1
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have he : (bellmanGauge q ^ 3) ^ (1 / 3 : ℝ) = bellmanGauge q := by
    rw [← Real.rpow_natCast_mul (bellmanGauge_nonneg q)]
    norm_num
  simp_all

/-- A negative homogeneous gauge bound has a uniform position-fiber power majorant. -/
theorem barrier_position_fiber_bound (beta : ℝ) (hb : beta ≤ 0)
    (f : (ℝ × ℝ) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ q ∈ bellmanPuncturedSet, |f q| ≤ C * bellmanGauge q ^ beta)
    (X v : ℝ) (hX : X ≠ 0) : |f (X, v)| ≤ C * |X| ^ (beta / 3) := by
  have hq : (X, v) ∈ bellmanPuncturedSet := fun he => hX (congrArg Prod.fst he)
  have hl := barrier_position_gauge_lower (X, v)
  have hh := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos (abs_pos.mpr hX) _) hl hb
  rw [← Real.rpow_mul (abs_nonneg X)] at hh
  have he : (1 / 3) * beta = beta / 3 := by ring
  rw [he] at hh
  exact (hbound _ hq).trans (mul_le_mul_of_nonneg_left hh hC)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
