/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.DegreeBound
import CCDN.AuxiliaryPolynomial.HypersurfacePositionHeight

/-! A polynomial box cutoff from the homogeneous coefficient-height bound.
The constants are explicit; only their dependence on dimension is needed in
the affine auxiliary-polynomial theorem. -/

@[expose] public section
namespace CCDN

private lemma box_le_of_logarithmic_height_bound {A B N D : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hN : 1 ≤ N) (hD : 0 ≤ D)
    (hheight : B / A ≤ N * Real.log N + N * D * Real.log B) :
    B ≤ 4 * A ^ 2 * N ^ 4 * (D + 1) ^ 2 := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hlogN : Real.log N ≤ N := Real.log_le_self hN0
  have hlogB : Real.log B ≤ 2 * Real.sqrt B := by
    have hh := Real.log_le_rpow_div hB0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at hh
    linarith
  have ht : 1 ≤ Real.sqrt B := by
    simp_all
  have ht0 : 0 < Real.sqrt B := by linarith
  have hNsq : N ≤ N ^ 2 := by nlinarith
  have hfirst : N * Real.log N ≤ N ^ 2 * Real.sqrt B := by
    calc
      _ ≤ N ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hlogN hN0]
      _ ≤ _ := le_mul_of_one_le_right (sq_nonneg N) ht
  have hsecond : N * D * Real.log B ≤ 2 * N ^ 2 * D * Real.sqrt B := by
    calc
      _ ≤ N * D * (2 * Real.sqrt B) :=
        mul_le_mul_of_nonneg_left hlogB (mul_nonneg hN0 hD)
      _ ≤ N ^ 2 * D * (2 * Real.sqrt B) := by gcongr
      _ = _ := by ring
  have hmain : B ≤ (A * N ^ 2 * (1 + 2 * D)) * Real.sqrt B := by
    have hh := (div_le_iff₀ hA0).mp hheight
    have hh' := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hA0.le
    linarith
  have hroot : Real.sqrt B ≤ A * N ^ 2 * (1 + 2 * D) := by
    apply (mul_le_mul_iff_right₀ ht0).mp
    grind
  have hroot' : Real.sqrt B ≤ 2 * A * N ^ 2 * (D + 1) := by
    have hh : 0 ≤ A * N ^ 2 := by positivity
    linarith
  have hh := pow_le_pow_left₀ ht0.le hroot' 2
  grind

/-- If the constant-coefficient prime choice fails while the coefficient
height obeys the determinant bound, the box is polynomially bounded in d. -/
theorem affine_coefficient_height_cutoff (n d : ℕ) {A B : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hheight : B / A ≤ ((n + d).choose d : ℝ) * Real.log ((n + d).choose d) +
      ((n + d).choose d : ℝ) * d * Real.log B) :
    B ≤ 4 * A ^ 2 * ((d : ℝ) + 1) ^ (4 * n + 2) := by
  have hN : (1 : ℝ) ≤ (n + d).choose d := by
    exact_mod_cast Nat.choose_pos (show d ≤ n + d by omega)
  have hbound := box_le_of_logarithmic_height_bound hA hB hN (Nat.cast_nonneg d) hheight
  have hcount : ((n + d).choose d : ℝ) ≤ ((d : ℝ) + 1) ^ n := by
    rw [← Nat.choose_symm_add, Nat.add_comm n d]
    exact_mod_cast Nat.choose_add_le_add_one_pow d n
  calc
    B ≤ 4 * A ^ 2 * ((n + d).choose d : ℝ) ^ 4 * ((d : ℝ) + 1) ^ 2 := hbound
    _ ≤ 4 * A ^ 2 * (((d : ℝ) + 1) ^ n) ^ 4 * ((d : ℝ) + 1) ^ 2 := by
      gcongr
    _ = _ := by ring

/-- The excess projective exponent costs a dimension constant on a polynomial box. -/
theorem polynomial_box_root_power_bound {n d k : ℕ} (hd : 0 < d) {S B : ℝ}
    (hS : 1 ≤ S) (hB : 1 ≤ B) (hbound : B ≤ S * ((d : ℝ) + 1) ^ k) :
    B ^ scaleExponent n d ≤ Real.exp (Real.log S + (k : ℝ) * (n + 2 : ℝ)) := by
  have hlog := Real.log_le_log (by linarith : 0 < B) hbound
  rw [Real.log_mul (by linarith) (by positivity), Real.log_pow] at hlog
  have hlogd := log_nat_add_one_le_degreeRoot (n := n) hd
  have hroot : 1 ≤ degreeRoot n d := Real.one_le_rpow (by exact_mod_cast hd) (by positivity)
  rw [Real.rpow_def_of_pos (by linarith), Real.exp_le_exp, ← div_eq_mul_one_div,
    div_le_iff₀ (by positivity)]
  have hSlog := Real.log_nonneg hS
  calc
    _ ≤ Real.log S + (k : ℝ) * ((n + 2 : ℝ) * degreeRoot n d) := hlog.trans (by gcongr)
    _ ≤ (Real.log S + (k : ℝ) * (n + 2 : ℝ)) * degreeRoot n d := by
      nlinarith only [mul_le_mul_of_nonneg_left hroot hSlog]
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) (by simp)) (by positivity)

end CCDN
