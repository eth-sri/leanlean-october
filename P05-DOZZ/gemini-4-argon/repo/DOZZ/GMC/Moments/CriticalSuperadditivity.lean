/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Strict power superadditivity used to rule out a finite critical GMC moment. -/

@[expose] public section

namespace DOZZ.Proofs

/-- For `p > 1`, the `p`th power is strictly superadditive on two positive masses. -/
theorem rpow_add_gt_add_rpow_of_pos {x y p : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hp : 1 < p) :
    x ^ p + y ^ p < (x + y) ^ p := by
  let s := x + y
  let u := x / s
  let v := y / s
  have hs : 0 < s := by dsimp [s]; positivity
  have hu : 0 < u ∧ u < 1 := by
    constructor
    · dsimp [u]
      exact div_pos hx hs
    · dsimp [u, s]
      exact (div_lt_one hs).2 (by linarith)
  have hv : 0 < v ∧ v < 1 := by
    constructor
    · dsimp [v]
      exact div_pos hy hs
    · dsimp [v, s]
      exact (div_lt_one hs).2 (by linarith)
  have hsPow := Real.rpow_pos_of_pos hs p
  calc
    x ^ p + y ^ p < u * s ^ p + v * s ^ p := add_lt_add (by rw [(show x ^ p = u ^ p * s ^ p by rw [(show x = u * s by dsimp [u]; field_simp [ne_of_gt hs]), Real.mul_rpow hu.1.le hs.le])]; exact mul_lt_mul_of_pos_right (Real.rpow_lt_self_of_lt_one hu.1 hu.2 hp) hsPow) (by rw [(show y ^ p = v ^ p * s ^ p by rw [(show y = v * s by dsimp [v]; field_simp [ne_of_gt hs]), Real.mul_rpow hv.1.le hs.le])]; exact mul_lt_mul_of_pos_right (Real.rpow_lt_self_of_lt_one hv.1 hv.2 hp) hsPow)
    _ = s ^ p := by rw [← add_mul, (show u + v = 1 by dsimp [u, v, s]; field_simp [ne_of_gt hs]), one_mul]
    _ = (x + y) ^ p := by rfl

/-- A four-tile version of strict power superadditivity, for the critical square partition. -/
theorem rpow_four_sum_gt_sum_of_pos {a b c d p : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hp : 1 < p) :
    a ^ p + b ^ p + c ^ p + d ^ p < (a + b + c + d) ^ p := by
  have hsum : 0 < a + b ∧ 0 < c + d := by constructor <;> positivity
  calc
    a ^ p + b ^ p + c ^ p + d ^ p =
        (a ^ p + b ^ p) + (c ^ p + d ^ p) := by ring
    _ < (a + b) ^ p + (c + d) ^ p := add_lt_add (rpow_add_gt_add_rpow_of_pos ha hb hp) (rpow_add_gt_add_rpow_of_pos hc hd hp)
    _ < ((a + b) + (c + d)) ^ p := (rpow_add_gt_add_rpow_of_pos hsum.1 hsum.2 hp)
    _ = (a + b + c + d) ^ p := by congr 1; ring

end DOZZ.Proofs
