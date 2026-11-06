module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! # The finite square-root decay power sum in timed entrance counting -/

public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open scoped BigOperators

variable (q : ℝ)

/-- The literal time-decay sequence has the source power growth for `1 < q < 2`. -/
theorem time_decay_power_sum_le  (hq : 1 < q) (hq2 : q < 2) (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), (1 + (i : ℝ)) ^ (-q / 2)) ≤
      (1 + 1 / (1 - q / 2)) * ((N : ℝ) + 1) ^ (1 - q / 2) := by
  let f := fun x : ℝ => x ^ (-q / 2)
  have hb : 0 < 1 - q / 2 := by linarith
  have he : -1 < -q / 2 := by linarith
  have hf : AntitoneOn f (Icc 1 (1 + N)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by grind) hxy (by linarith)
  have hs := hf.sum_le_integral (a := N) (x₀ := 1)
  have hi : (∫ x in (1)..1 + N, f x) =
      (((1 + N) ^ (1 - q / 2) - 1) / (1 - q / 2)) := by
    rw [integral_rpow (Or.inl he), Real.one_rpow]
    ring
  rw [hi] at hs
  have hsum : (∑ i ∈ Finset.range (N + 1), (1 + (i : ℝ)) ^ (-q / 2)) =
      1 + ∑ i ∈ Finset.range N, f (1 + ((i + 1 : ℕ))) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, add_zero, Real.one_rpow]
    linarith
  rw [hsum]
  have hp : 1 ≤ ((N : ℝ) + 1) ^ (1 - q / 2) :=
    Real.one_le_rpow (by linarith) hb.le
  have ha : 1 + N = (N : ℝ) + 1 := add_comm _ _
  rw [ha] at hs
  have hs' := add_le_add_right hs 1
  apply hs'.trans
  have hle : ((N + 1) ^ (1 - q / 2) - 1) / (1 - q / 2) ≤
      (N + 1) ^ (1 - q / 2) / (1 - q / 2) :=
    div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) hb.le
  grind

/-- The observation-horizon count converts to the source factor `(1+R/r)^(2-q)`. -/
theorem time_decay_power_sum_horizon_le  (hq : 1 < q) (hq2 : q < 2)
    (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r) (N : ℕ)
    (hN : (N : ℝ) ≤ 2 + (R / r) ^ 2) :
    (∑ i ∈ Finset.range (N + 1), (1 + (i : ℝ)) ^ (-q / 2)) ≤
      ((1 + 1 / (1 - q / 2)) * (3 : ℝ) ^ (1 - q / 2)) *
        (1 + R / r) ^ (2 - q) := by
  have hb : 0 < 1 - q / 2 := by linarith
  have hx : 0 ≤ R / r := div_nonneg hR hr.le
  have hs : N + 1 ≤ 3 * (1 + R / r) ^ 2 := by nlinarith
  have hp := Real.rpow_le_rpow (by positivity) hs hb.le
  have he : (3 * (1 + R / r) ^ 2) ^ (1 - q / 2) =
      (3) ^ (1 - q / 2) * (1 + R / r) ^ (2 - q) := by
    rw [Real.mul_rpow (by norm_num) (sq_nonneg _),
      ← Real.rpow_natCast_mul (by linarith)]
    ring
  rw [he] at hp
  apply (time_decay_power_sum_le q hq hq2 N).trans
  have hC : 0 ≤ 1 + 1 / (1 - q / 2) := by positivity
  exact (mul_le_mul_of_nonneg_left hp hC).trans_eq (mul_assoc _ _ _).symm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
