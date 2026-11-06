/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Plane.ScaledPlaneCount
import CCDN.ForMathlib.Log

/-! The scaling-prime interval yields the affine box exponent 1/d. These
numerical bounds are independent of the coefficient height. -/

namespace CCDN
open Real

section
variable {d : ℕ} (hd : 0 < d)
include hd

lemma scaled_box_power_ratio_le {A B p : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hp : 0 < p) (hBp : B ≤ A * p) :
    (((d : ℝ) + 1) * B) ^ (2 / (d : ℝ)) / p ^ (1 / (d : ℝ)) ≤
      Real.exp 2 * A * B ^ (1 / (d : ℝ)) := by
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hB0 : 0 < B := by linarith
  have hdplus : (0 : ℝ) < d + 1 := by linarith
  have hlog := Real.log_add_one_le_self hd0.le
  have hdeg : ((d : ℝ) + 1) ^ (2 / (d : ℝ)) ≤ Real.exp 2 := by
    rw [Real.rpow_def_of_pos hdplus]
    apply Real.exp_le_exp.mpr
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd0).mpr
    linarith
  have hquot : (B / p) ^ (1 / (d : ℝ)) ≤ A := by
    have hbase := (div_le_iff₀ hp).mpr hBp
    have h := Real.rpow_le_rpow (div_nonneg hB0.le hp.le) hbase
      (show (0 : ℝ) ≤ 1 / d by positivity)
    apply h.trans
    simpa using Real.rpow_le_rpow_of_exponent_le hA
      (show (1 : ℝ) / d ≤ 1 by bound)
  have he : (((d : ℝ) + 1) * B) ^ (2 / (d : ℝ)) / p ^ (1 / (d : ℝ)) =
      ((d : ℝ) + 1) ^ (2 / (d : ℝ)) * (B / p) ^ (1 / (d : ℝ)) * B ^ (1 / (d : ℝ)) := by
    rw [Real.mul_rpow hdplus.le hB0.le, Real.div_rpow hB0.le hp.le, show (2 : ℝ) / d = 1 / d + 1 / d by ring, Real.rpow_add hB0]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hdeg hquot (Real.rpow_nonneg (div_nonneg hB0.le hp.le) _) (Real.exp_pos _).le)
    (Real.rpow_nonneg hB0.le _)

lemma scaled_auxiliary_degree_bound_le {A B p C : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hp : 1 ≤ p) (hpB : p ≤ B) (hBp : B ≤ A * p) :
    (d : ℝ) * scaledPlaneAuxiliaryDegreeBound d C (((d : ℝ) + 1) * B) p ≤
      (4 + 2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * Real.exp 2 * A) *
        (d : ℝ) ^ 3 * B ^ (1 / (d : ℝ)) * (Real.log B + d) := by
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hB0 : 0 < B := by linarith
  have hp0 : 0 < p := by linarith
  have hlogB := Real.log_nonneg hB
  have hlogp := Real.log_nonneg hp
  have hlogpB := Real.log_le_log hp0 hpB
  have hlogR : Real.log ((d + 1) * B) ≤ d + Real.log B := by
    rw [Real.log_mul (by positivity) hB0.ne']
    linarith [Real.log_add_one_le_self hd0.le]
  let Q := B ^ (1 / (d : ℝ))
  let E := 2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14
  have hQ : 1 ≤ Q := Real.one_le_rpow hB (by positivity)
  have hE : 0 ≤ E := by positivity
  have hratio := scaled_box_power_ratio_le hd hA hB hp0 hBp
  have hnum : 0 ≤ 1 + Real.log p / d := by positivity
  have hnumB : 1 + Real.log p / d ≤ 1 + Real.log B / d := by gcongr
  have hterm : E * d ^ 3 * (1 + Real.log p / d) *
        ((((d : ℝ) + 1) * B) ^ (2 / (d : ℝ)) / p ^ (1 / (d : ℝ))) ≤
      E * Real.exp 2 * A * d ^ 2 * Q * (Real.log B + d) := by
    have hh := mul_le_mul hnumB hratio
      (Real.rpow_nonneg (show 0 ≤ ((d : ℝ) + 1) * B by positivity) _ |> fun h =>
        div_nonneg h (Real.rpow_nonneg hp0.le _)) (by grind)
    have ht := mul_le_mul_of_nonneg_left hh (mul_nonneg hE (pow_nonneg hd0.le 3))
    convert ht using 1
    · ring
    · grind
  have hrest : d + Real.log ((d + 1) * B) + 2 ≤
      4 * d ^ 2 * Q * (Real.log B + d) := by
    have hd2 : (1 : ℝ) ≤ d ^ 2 := by nlinarith
    have hprod := one_le_mul_of_one_le_of_one_le hd2 hQ
    nlinarith
  have hb : scaledPlaneAuxiliaryDegreeBound d C ((d + 1) * B) p ≤
      (4 + E * Real.exp 2 * A) * (d : ℝ) ^ 2 * Q * (Real.log B + d) := by
    unfold scaledPlaneAuxiliaryDegreeBound
    calc
      _ = (d + Real.log ((d + 1) * B) + 2) + E * d ^ 3 *
          (1 + Real.log p / d) *
          ((((d : ℝ) + 1) * B) ^ (2 / (d : ℝ)) / p ^ (1 / (d : ℝ))) := by grind
      _ ≤ 4 * d ^ 2 * Q * (Real.log B + d) +
          E * Real.exp 2 * A * d ^ 2 * Q * (Real.log B + d) := add_le_add hrest hterm
      _ = _ := by ring
  have ht := mul_le_mul_of_nonneg_left hb hd0.le
  convert ht using 1
  dsimp [E, Q]
  ring

end

