module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxConcentrationSetting
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

/-! # The kinetic radius of a scaled box -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set
open scoped ENNReal

/-- The literal box has the precise homogeneous gauge radius. -/
theorem box_rho_le {A0 r Y : ℝ} (hA0 : 0 < A0) (hr : 0 < r)
    {z : Z} (hz : z ∈ box A0 r Y) :
    bellmanGauge (z.1-Y,z.2) ≤ (A0^2+A0^6)^(1/6 : ℝ)*r := by
  have hx := pow_le_pow_left₀ (abs_nonneg (z.1-Y)) hz.1 2
  have hv := pow_le_pow_left₀ (abs_nonneg z.2) hz.2 6
  rw [sq_abs] at hx
  rw [pow_abs, abs_of_nonneg (Even.pow_nonneg (by decide) z.2)] at hv
  have hs : (z.1-Y)^2+z.2^6 ≤ (A0^2+A0^6)*r^6 := by
    calc
      _ ≤ (A0*r^3)^2+(A0*r)^6 := add_le_add hx hv
      _ = _ := by ring
  have ha : 0 ≤ A0^2+A0^6 := by positivity
  have hb := Real.rpow_le_rpow (bellmanGaugePower_nonneg (z.1-Y,z.2)) hs
    (by norm_num : 0 ≤ (1/6 : ℝ))
  have he : (r^6)^(1/6 : ℝ) = r := by
    convert Real.pow_rpow_inv_natCast hr.le (by decide : 6 ≠ 0) using 1
    norm_num
  have hm := Real.mul_rpow (z := (1/6)) ha (pow_nonneg hr.le 6)
  rw [he] at hm
  exact hb.trans_eq hm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
