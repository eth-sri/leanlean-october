/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.ParetoCoefficient
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
/-! First-order domination of the discarded bounded-maximum part of Williams' model. -/
public section
open MeasureTheory Set Filter
namespace DOZZ.Proofs

/-- The signed inverse-power increment has its exact first-order majorant. -/
theorem reflected_negative_add_increment_bound (p A t : ℝ) (hp : 0 < p)
    (hA : 0 < A) (ht : 0 ≤ t) :
    |(A+t)^(-p)-A^(-p)| ≤ p*A^(-p-1)*t := by
  have hratio  := div_nonneg ht hA.le
  have h := reflected_negative_power_increment p (t/A) hp hratio
  have he : A+t = A*(1+t/A) := by field_simp
  have hs : (A+t)^(-p)-A^(-p) = A^(-p)*((1+t/A)^(-p)-1) := by
    rw [he, Real.mul_rpow hA.le (by linarith only [hratio])]
    ring
  rw [hs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hA.le _)]
  have hb := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hA.le (-p))
  calc
    A^(-p)*|(1+t/A)^(-p)-1| ≤ A^(-p)*(p*(t/A)) := hb
    _ = p*A^(-p-1)*t := by rw [Real.rpow_sub_one hA.ne']; ring

/-- A bounded Williams maximum and a cut below the full reflection mass are dominated by
its first moment, with the explicit retained inverse-power factor. -/
theorem reflected_bounded_maximum_increment_bound (p A b γ H m J j : ℝ)
    (hp : 0 < p) (hA : 0 < A) (hb : 0 ≤ b) (hγ : 0 ≤ γ)
    (hm : m ≤ H) (hj : 0 ≤ j) (hjJ : j ≤ J) :
    |(A+b*Real.exp (γ*m)*j)^(-p)-A^(-p)| ≤
      p*A^(-p-1)*b*Real.exp (γ*H)*J := by
  have ht : 0 ≤ b*Real.exp (γ*m)*j := by positivity
  have hexp  :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hm hγ)
  have hmass  :=
    mul_le_mul (mul_le_mul_of_nonneg_left hexp hb) hjJ hj (by positivity)
  calc
    _ ≤ p*A^(-p-1)*(b*Real.exp (γ*m)*j) :=
      reflected_negative_add_increment_bound p A _ hp hA ht
    _ ≤ p*A^(-p-1)*(b*Real.exp (γ*H)*J) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

end DOZZ.Proofs
