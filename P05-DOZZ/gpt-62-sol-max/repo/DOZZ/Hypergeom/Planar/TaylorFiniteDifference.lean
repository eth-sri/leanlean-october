/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Calculus.Taylor
public import DOZZ.Hypergeom.Planar.TaylorTail

/-! Smooth radial-power calculations away from the moving singularity. -/

@[expose] public section

open Filter
open Set
open scoped Topology

namespace DOZZ.Proofs

/-- Squared norm along a real coordinate line through `x`. -/
noncomputable def radialShiftSq (x : ℂ) (t : ℝ) : ℝ :=
  ‖x‖ ^ 2 + x.re * t * 2 + t ^ 2

/-- First derivative of the `p`-power of `radialShiftSq`. -/
noncomputable def radialShiftFirstDerivative (p : ℝ) (x : ℂ) (t : ℝ) : ℝ :=
  p * radialShiftSq x t ^ (p - 1) * (2 * x.re + 2 * t)

/-- Derivative of the squared norm along a real coordinate line. -/
theorem hasDerivAt_radialShiftSq (x : ℂ) (t : ℝ) :
    HasDerivAt (radialShiftSq x) (2 * x.re + 2 * t) t := by
  change HasDerivAt (fun s : ℝ => ‖x‖ ^ 2 + x.re * s * 2 + s ^ 2) _ _
  have hlin : HasDerivAt (fun s : ℝ => x.re * s * 2) (2 * x.re) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_id t).const_mul (2 * x.re)
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    convert (hasDerivAt_id t).pow 2 using 1
    · rfl
    · norm_num
  convert (hasDerivAt_const t (‖x‖ ^ 2)).add (hlin.add hsq) using 1
  · ext s
    simp only [Pi.add_apply]
    ring
  · ring

/-- Derivative of a real power of the squared norm along a coordinate line, away from its zero. -/
theorem hasDerivAt_radialShiftRpow (p : ℝ) (x : ℂ) (t : ℝ)
    (hpos : 0 < radialShiftSq x t) :
    HasDerivAt (fun s : ℝ => radialShiftSq x s ^ p)
      (radialShiftFirstDerivative p x t) t := by
  have hq := hasDerivAt_radialShiftSq x t
  have hp := (Real.hasDerivAt_rpow_const (x := radialShiftSq x t) (p := p)
    (Or.inl hpos.ne')).comp t hq
  assumption

/-- The coordinate formula for the squared norm in `ℂ`. -/
theorem radialShiftSq_eq_normSq (x : ℂ) (t : ℝ) :
    radialShiftSq x t = Complex.normSq (x + (t : ℂ)) := by
  rw [Complex.normSq_add]
  simp [radialShiftSq, Complex.normSq_ofReal, Complex.mul_re]
  rw [Complex.normSq_eq_norm_sq]
  ring_nf

/-- A norm power is a real power of the squared norm. -/
private theorem norm_rpow_eq_norm_sq_rpow (x : ℂ) (k : ℝ) :
    ‖x‖ ^ k = (‖x‖ ^ 2) ^ (k / 2) := by
  calc
    ‖x‖ ^ k = ‖x‖ ^ (2 * (k / 2)) := by congr 1; ring
    _ = (‖x‖ ^ 2) ^ (k / 2) := Real.rpow_natCast_mul (norm_nonneg x) 2 (k / 2)


section
variable (p : ℝ) (x : ℂ) (hx : x ≠ 0)
include hx

/-- The derivative of the first derivative of `‖x + t‖^(2p)` at `t=0`, for `x ≠ 0`.
This is the one-dimensional second-derivative calculation used away from the collision point. -/
theorem hasDerivAt_radialShiftFirstDerivative :
    HasDerivAt (radialShiftFirstDerivative p x)
      (p * (p - 1) * (‖x‖ ^ 2) ^ (p - 2) * (2 * x.re) ^ 2 +
        p * (‖x‖ ^ 2) ^ (p - 1) * 2) 0 := by
  let q  := radialShiftSq x
  have hq : HasDerivAt q (2 * x.re) 0 := by
    change HasDerivAt (fun t : ℝ => ‖x‖ ^ 2 + x.re * t * 2 + t ^ 2) _ _
    have hlin : HasDerivAt (fun t : ℝ => x.re * t * 2) (2 * x.re) 0 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (hasDerivAt_id (0 : ℝ)).const_mul (2 * x.re)
    have hsq : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
      convert (hasDerivAt_id (0 : ℝ)).pow 2 using 1
      · rfl
      · norm_num
    convert (hasDerivAt_const (0 : ℝ) (‖x‖ ^ 2)).add (hlin.add hsq)
      using 1
    · ext t
      simp only [Pi.add_apply]
      ring
    · ring
  have hq0 : q 0 = ‖x‖ ^ 2 := by simp [q, radialShiftSq]
  have hqpos : 0 < q 0 := by rw [hq0]; positivity
  have hpow : HasDerivAt (fun t : ℝ => q t ^ (p - 1))
      ((p - 1) * q 0 ^ (p - 2) * (2 * x.re)) 0 := by
    convert (Real.hasDerivAt_rpow_const (x := q 0) (p := p - 1)
      (Or.inl hqpos.ne')).comp 0 hq using 1
    · rfl
    · rw [show p - 1 - 1 = p - 2 by ring]
  have hlin : HasDerivAt (fun t : ℝ => 2 * x.re + 2 * t) 2 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)).const_add (2 * x.re)
      using 1 <;> norm_num
  have hprod := (hpow.mul hlin).const_mul p
  have hform : radialShiftFirstDerivative p x =
      fun t => p * q t ^ (p - 1) * (2 * x.re + 2 * t) := by
    funext t
    rfl
  rw [hform]
  convert hprod using 1
  · ext t
    simp only [Pi.mul_apply]
    ring
  · rw [hq0]
    ring

/-- The second derivative of a radial power along a real coordinate line, at its nonzero center. -/
theorem hasDerivAt_deriv_radialShiftRpow :
    HasDerivAt (fun t : ℝ => deriv (fun s => radialShiftSq x s ^ p) t)
      (p * (p - 1) * (‖x‖ ^ 2) ^ (p - 2) * (2 * x.re) ^ 2 +
        p * (‖x‖ ^ 2) ^ (p - 1) * 2) 0 := by
  let q  := radialShiftSq x
  have hq0 : q 0 = ‖x‖ ^ 2 := by simp [q, radialShiftSq]
  have hqpos : 0 < q 0 := by rw [hq0]; positivity
  have hqcont : Continuous q := by
    change Continuous (fun t : ℝ => ‖x‖ ^ 2 + x.re * t * 2 + t ^ 2)
    fun_prop
  have hqposEv  :=
    hqcont.continuousAt.eventually (isOpen_Ioi.mem_nhds hqpos)
  have hderivEq : deriv (fun s => q s ^ p) =ᶠ[𝓝 (0 : ℝ)]
      radialShiftFirstDerivative p x := by
    filter_upwards [hqposEv] with t ht
    exact (hasDerivAt_radialShiftRpow p x t ht).deriv
  have hsecond := hasDerivAt_radialShiftFirstDerivative p x hx
  exact hsecond.congr_of_eventuallyEq hderivEq

end

section
variable (k : ℝ) (x : ℂ) (hx : x ≠ 0)
include hx

/-- The second derivative of `‖x+t‖^k` at `t=0`, written through the squared norm. -/
theorem hasDerivAt_deriv_norm_rpow_shift :
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ => ‖x + (s : ℂ)‖ ^ k) t)
      ((k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) *
          (2 * x.re) ^ 2 +
        (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2) 0 := by
  have hfun : (fun t : ℝ => ‖x + (t : ℂ)‖ ^ k) =
      (fun t => radialShiftSq x t ^ (k / 2)) := by
    funext t
    rw [norm_rpow_eq_norm_sq_rpow, ← Complex.normSq_eq_norm_sq, radialShiftSq_eq_normSq]
  have hderiv : (fun t : ℝ => deriv (fun s : ℝ => ‖x + (s : ℂ)‖ ^ k) t) =
      (fun t => deriv (fun s : ℝ => radialShiftSq x s ^ (k / 2)) t) := by
    rw [hfun]
  have hsecond := hasDerivAt_deriv_radialShiftRpow (k / 2) x hx
  exact hsecond.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hderiv)


/-- The sum of the two coordinate second derivatives is the planar Laplacian
coefficient `k^2 ‖x‖^(k-2)`. -/
theorem radial_rpow_laplacian_coefficient :
    ((k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) *
          (2 * x.re) ^ 2 +
        (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2) +
      ((k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) *
          (2 * x.im) ^ 2 +
        (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2) =
      k ^ 2 * ‖x‖ ^ (k - 2) := by
  let p  := k / 2
  let r  := ‖x‖ ^ 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hcoord : (2 * x.re) ^ 2 + (2 * x.im) ^ 2 = 4 * r := by
    dsimp [r]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hpow : r ^ (p - 2) * r = r ^ (p - 1) := by
    calc
      r ^ (p - 2) * r = r ^ (p - 2) * r ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = r ^ ((p - 2) + 1) := (Real.rpow_add hr (p - 2) 1).symm
      _ = r ^ (p - 1) := by congr 1; ring
  have hnormpow : r ^ (p - 1) = ‖x‖ ^ (k - 2) := by
    dsimp [p, r]
    rw [show k / 2 - 1 = (k - 2) / 2 by ring]
    exact (norm_rpow_eq_norm_sq_rpow x (k - 2)).symm
  calc
    _ = p * (p - 1) * r ^ (p - 2) *
          ((2 * x.re) ^ 2 + (2 * x.im) ^ 2) + 4 * p * r ^ (p - 1) := by
            ring
    _ = p * (p - 1) * r ^ (p - 2) * (4 * r) +
          4 * p * r ^ (p - 1) := by rw [hcoord]
    _ = 4 * p ^ 2 * r ^ (p - 1) := by rw [← hpow]; ring
    _ = k ^ 2 * ‖x‖ ^ (k - 2) := by
          rw [hnormpow]
          dsimp [p]
          ring

end

/-- The numerator shared by the real and imaginary centered second differences. -/
noncomputable def radialSecondDiff (k : ℝ) (x y : ℂ) : ℝ :=
  ‖x + y‖ ^ k + ‖x - y‖ ^ k - 2 * ‖x‖ ^ k

/-- Centered real second difference of the radial power. -/
noncomputable def normPowerRealSecondDifference (k t : ℝ) (x : ℂ) : ℝ :=
  radialSecondDiff k x (t : ℂ) / t ^ 2

/-- The sum of the real and imaginary second-difference quotients. -/
noncomputable def normPowerDiscreteLaplacian (k t : ℝ) (x : ℂ) : ℝ :=
  (‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k +
    ‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k - 4 * ‖x‖ ^ k) / t ^ 2

theorem normPowerDiscreteLaplacian_eq (k t : ℝ) (x : ℂ) :
    normPowerDiscreteLaplacian k t x = normPowerRealSecondDifference k t x +
      radialSecondDiff k x ((t : ℂ) * Complex.I) / t ^ 2 := by
  unfold normPowerDiscreteLaplacian normPowerRealSecondDifference radialSecondDiff
  ring

/-- Majorant constant valid for steps of any size. -/
noncomputable def radialCenteredConstant (k : ℝ) : ℝ :=
  2 * radialTaylorConstant k + 2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k)

section
variable (k : ℝ) (hk : 0 < k) (hk₂ : k < 2)
include hk hk₂

section
variable (x y : ℂ)

/-- A centered second difference of a radial power is quadratically bounded when the
increment is at most half the distance to the origin. -/
theorem norm_rpow_centered_difference_le (hx : x ≠ 0) (hy : ‖y‖ ≤ ‖x‖ / 2) :
    |radialSecondDiff k x y| ≤ 2 * radialTaylorConstant k * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by
  let q := y / x
  have hxpos := norm_pos_iff.mpr hx
  have hq : ‖q‖ ≤ 1 / 2 := by
    rw [show ‖q‖ = ‖y‖ / ‖x‖ by simp [q], div_le_iff₀ hxpos]
    linarith
  have plus : x + y = x * (1 + q) := by dsimp [q]; field_simp
  have minus : x - y = x * (1 - q) := by dsimp [q]; field_simp
  let R := fun u : ℂ => ‖1 - u‖ ^ k - 1 + k * u.re
  have hR (u : ℂ) (hu : ‖u‖ ≤ 1 / 2) : |R u| ≤ radialTaylorConstant k * ‖u‖ ^ 2 :=
    norm_unit_taylor_remainder_le k hk hk₂ u hu
  have hpair : radialSecondDiff k x y = ‖x‖ ^ k * (R q + R (-q)) := by
    unfold radialSecondDiff
    rw [plus, minus]
    simp only [R, sub_neg_eq_add, Complex.neg_re, norm_mul, Real.mul_rpow (norm_nonneg x) (norm_nonneg _)]
    ring
  rw [hpair, abs_mul, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ‖x‖ ^ k * (|R q| + |R (-q)|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
    _ ≤ ‖x‖ ^ k * (radialTaylorConstant k * ‖q‖ ^ 2 + radialTaylorConstant k * ‖-q‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add (hR q hq) (hR (-q) (by simpa using hq))) (by positivity)
    _ = _ := by
      simp only [q, norm_neg, norm_div, div_pow]
      rw [Real.rpow_sub hxpos, Real.rpow_two]
      ring

/-- A global second-difference majorant, including increments that reach or cross the origin.
The constant is deliberately explicit so it can be used under an integral. -/
theorem norm_rpow_centered_difference_le_global (hx : x ≠ 0) :
    |radialSecondDiff k x y| ≤
      radialCenteredConstant k * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by
  let C  := radialTaylorConstant k
  let B : ℝ := 2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k)
  have hC : 0 ≤ C := by
    exact radialTaylorConstant_nonneg k hk.le hk₂.le
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  by_cases hsmall : ‖y‖ ≤ ‖x‖ / 2
  · have hlocal := norm_rpow_centered_difference_le k hk hk₂ x y hx hsmall
    have hweight : 0 ≤ ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by positivity
    calc
      _ ≤ 2 * C * (‖y‖ ^ 2 * ‖x‖ ^ (k - 2)) := by
        simpa [C, mul_assoc] using hlocal
      _ ≤ (2 * C + B) * (‖y‖ ^ 2 * ‖x‖ ^ (k - 2)) := mul_le_mul_of_nonneg_right (by linarith) hweight
      _ = (2 * C + B) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by ring
  · have hlarge  := lt_of_not_ge hsmall
    have hypos  := lt_of_le_of_lt (by positivity) hlarge
    have hxle : ‖x‖ ≤ 2 * ‖y‖ := by linarith
    have hplus : ‖x + y‖ ≤ 3 * ‖y‖ := by
      calc
        ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
        _ ≤ 3 * ‖y‖ := by linarith
    have hminus : ‖x - y‖ ≤ 3 * ‖y‖ := by
      calc
        ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ 3 * ‖y‖ := by linarith
    have hplusPow  :=
      Real.rpow_le_rpow (norm_nonneg _) hplus hk.le
    have hminusPow  :=
      Real.rpow_le_rpow (norm_nonneg _) hminus hk.le
    have hxPow  :=
      Real.rpow_le_rpow (norm_nonneg _) hxle hk.le
    have hraw : |radialSecondDiff k x y| ≤
        2 * (3 * ‖y‖) ^ k + 2 * (2 * ‖y‖) ^ k := by
      calc
        _ ≤ |‖x + y‖ ^ k + ‖x - y‖ ^ k| + |2 * ‖x‖ ^ k| := abs_sub _ _
        _ = ‖x + y‖ ^ k + ‖x - y‖ ^ k + 2 * ‖x‖ ^ k := by
          rw [abs_of_nonneg (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
            (Real.rpow_nonneg (norm_nonneg _) _)), abs_of_nonneg (by positivity)]
        _ ≤ 2 * (3 * ‖y‖) ^ k + 2 * (2 * ‖y‖) ^ k := by
          linarith
    have hmul3 : (3 * ‖y‖) ^ k = 3 ^ k * ‖y‖ ^ k :=
      Real.mul_rpow (by norm_num) (norm_nonneg y)
    have hmul2 : (2 * ‖y‖) ^ k = 2 ^ k * ‖y‖ ^ k :=
      Real.mul_rpow (by norm_num) (norm_nonneg y)
    have hySplit : ‖y‖ ^ k = ‖y‖ ^ 2 * ‖y‖ ^ (k - 2) := by
      calc
        ‖y‖ ^ k = ‖y‖ ^ ((2 : ℝ) + (k - 2)) := by congr 1; ring
        _ = ‖y‖ ^ (2 : ℝ) * ‖y‖ ^ (k - 2) := Real.rpow_add hypos _ _
        _ = ‖y‖ ^ 2 * ‖y‖ ^ (k - 2) :=
          congrArg (fun t : ℝ => t * ‖y‖ ^ (k - 2)) (Real.rpow_natCast ‖y‖ 2)
    have hhalf : (‖x‖ / 2) ^ (k - 2) =
        2 ^ (2 - k) * ‖x‖ ^ (k - 2) := by
      rw [show ‖x‖ / 2 = ‖x‖ * (1 / 2 : ℝ) by ring,
        Real.mul_rpow (norm_nonneg x) (by norm_num : 0 ≤ (1 / 2 : ℝ)),
        show (1 / 2 : ℝ) ^ (k - 2) = 2 ^ (2 - k) by
          rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num), show 2 - k = -(k - 2) by ring, ← Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ))]]
      ring
    have hnegative : k - 2 ≤ 0 := by linarith
    have hdecrease : ‖y‖ ^ (k - 2) ≤ (‖x‖ / 2) ^ (k - 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hnegative
    have hyBound : ‖y‖ ^ k ≤
        ‖y‖ ^ 2 * (2 ^ (2 - k) * ‖x‖ ^ (k - 2)) := by
      rw [hySplit]
      exact mul_le_mul_of_nonneg_left (hdecrease.trans_eq hhalf) (sq_nonneg ‖y‖)
    calc
      _ ≤ 2 * (3 * ‖y‖) ^ k + 2 * (2 * ‖y‖) ^ k := hraw
      _ = 2 * (3 ^ k + 2 ^ k) * ‖y‖ ^ k := by rw [hmul3, hmul2]; ring
      _ ≤ B * (‖y‖ ^ 2 * ‖x‖ ^ (k - 2)) := by
        dsimp [B]
        calc
          2 * (3 ^ k + 2 ^ k) * ‖y‖ ^ k ≤
              2 * (3 ^ k + 2 ^ k) *
                (‖y‖ ^ 2 * (2 ^ (2 - k) * ‖x‖ ^ (k - 2))) :=
            mul_le_mul_of_nonneg_left hyBound (by positivity)
          _ = B * (‖y‖ ^ 2 * ‖x‖ ^ (k - 2)) := by dsimp [B]; ring
      _ ≤ (2 * C + B) * (‖y‖ ^ 2 * ‖x‖ ^ (k - 2)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (2 * C + B) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by ring

private theorem radial_divided_secondDiff_le (t : ℝ) (hx : x ≠ 0)
    (ht : t ≠ 0) (hy : ‖y‖ ^ 2 = t ^ 2) :
    |radialSecondDiff k x y / t ^ 2| ≤ radialCenteredConstant k * ‖x‖ ^ (k - 2) := by
  rw [abs_div, abs_of_nonneg (sq_nonneg t), div_le_iff₀ (sq_pos_of_ne_zero ht)]
  simpa only [hy, mul_right_comm (radialCenteredConstant k)] using
    norm_rpow_centered_difference_le_global k hk hk₂ x y hx

end

section
variable (x : ℂ) (t : ℝ) (hx : x ≠ 0) (ht : t ≠ 0)
include hx ht

/-- A global Riesz majorant for the real second difference at nonzero steps. -/
theorem normPowerRealSecondDifference_le :
    |normPowerRealSecondDifference k t x| ≤ radialCenteredConstant k * ‖x‖ ^ (k - 2) :=
  radial_divided_secondDiff_le k hk hk₂ x t t hx ht (by simp)

/-- The four-direction quotient is bounded by the sum of two directional estimates. -/
theorem norm_rpow_discrete_laplacian_le :
    |normPowerDiscreteLaplacian k t x| ≤ 2 * radialCenteredConstant k * ‖x‖ ^ (k - 2) := by
  rw [normPowerDiscreteLaplacian_eq]
  have hR := normPowerRealSecondDifference_le k hk hk₂ x t hx ht
  have hI := radial_divided_secondDiff_le k hk hk₂ x ((t : ℂ) * Complex.I) t hx ht (by simp)
  linarith [abs_add_le (normPowerRealSecondDifference k t x) (radialSecondDiff k x ((t : ℂ) * Complex.I) / t ^ 2)]

end

end

/-- Explicit second-order Taylor polynomial at an interior point of an open interval. -/
theorem taylorWithinEval_two_eq (f : ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s)
    (h0 : (0 : ℝ) ∈ s) (t : ℝ) (_ht : t ∈ s) :
    taylorWithinEval f 2 s 0 t =
      f 0 + t * deriv f 0 + (t ^ 2 / 2) * deriv (deriv f) 0 := by
  have h1 : iteratedDerivWithin 1 f s 0 = deriv f 0 := by
    have h := iteratedDerivWithin_of_isOpen_eq_iterate (n := 1) (f := f) hs h0
    assumption
  have h2 : iteratedDerivWithin 2 f s 0 = deriv (deriv f) 0 := by
    have h := iteratedDerivWithin_of_isOpen_eq_iterate (n := 2) (f := f) hs h0
    assumption
  simp only [taylorWithinEval_succ, taylor_within_zero_eval, h1, h2,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_zero, Nat.cast_one,
    zero_add, one_mul, inv_one, sub_zero, pow_one]
  ring

/-- For a function that is twice continuously differentiable near zero, the symmetric
second-difference quotient converges to its second derivative. -/
theorem central_second_difference_tendsto {f : ℝ → ℝ} {s : Set ℝ}
    (hs : Convex ℝ s) (hso : IsOpen s) (h0 : (0 : ℝ) ∈ s)
    (hf : ContDiffOn ℝ 2 f s) :
    Tendsto (fun t : ℝ => (f t + f (-t) - 2 * f 0) / t ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (deriv (deriv f) 0)) := by
  let P  := fun t => taylorWithinEval f 2 s 0 t
  have hsNhds  := hso.mem_nhds h0
  have hTaylor : Tendsto (fun t : ℝ => (f t - P t) / t ^ 2)
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    have h := Real.taylor_tendsto (f := f) (x₀ := (0 : ℝ)) (s := s) hs h0 hf
    rw [hso.nhdsWithin_eq h0] at h
    simpa [P] using h
  have hid : Tendsto (fun t : ℝ => t) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hid.neg
  have hposErr := hTaylor.comp hid
  have hnegErr : Tendsto (fun t : ℝ => (f (-t) - P (-t)) / t ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    convert hTaylor.comp hneg using 1
    ext t
    simp [P, pow_two]
  have hsum : Tendsto
      (fun t : ℝ => (deriv (deriv f) 0) +
        ((f t - P t) / t ^ 2 + (f (-t) - P (-t)) / t ^ 2))
      (𝓝[≠] (0 : ℝ)) (𝓝 (deriv (deriv f) 0)) := by
    have hsumErr := hposErr.add hnegErr
    simpa [add_assoc] using tendsto_const_nhds.add hsumErr
  have hne : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using ht
  have hmem : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), t ∈ s ∧ -t ∈ s := by
    filter_upwards [hid.eventually hsNhds, hneg.eventually hsNhds] with t ht₁ ht₂
    change t ∈ s at ht₁
    change -t ∈ s at ht₂
    exact ⟨ht₁, ht₂⟩
  have heq : (fun t : ℝ => (f t + f (-t) - 2 * f 0) / t ^ 2) =ᶠ[𝓝[≠] (0 : ℝ)]
      fun t => (deriv (deriv f) 0) +
        ((f t - P t) / t ^ 2 + (f (-t) - P (-t)) / t ^ 2) := by
    filter_upwards [hne, hmem] with t ht hmem
    obtain ⟨hts, hnts⟩ := hmem
    have hPt := taylorWithinEval_two_eq f s hso h0 t hts
    have hPnt := taylorWithinEval_two_eq f s hso h0 (-t) hnts
    dsimp [P]
    rw [hPt, hPnt]
    field_simp [ht]
    ring
  exact hsum.congr' heq.symm

section
variable (k : ℝ) (x : ℂ) (hx : x ≠ 0)
include hx

/-- The real-coordinate centered difference of `‖x+t‖^k` converges to its second derivative
at every nonzero center. -/
theorem norm_rpow_real_centered_difference_tendsto :
    Tendsto (fun t : ℝ =>
      (‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k - 2 * ‖x‖ ^ k) / t ^ 2)
      (𝓝[≠] (0 : ℝ))
      (𝓝 ((k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) *
          (2 * x.re) ^ 2 + (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2)) := by
  let ρ  := ‖x‖ / 2
  let s  := Ioo (-ρ) ρ
  let f : ℝ → ℝ := fun t => ‖x + (t : ℂ)‖ ^ k
  let q  := radialShiftSq x
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hxpos  := norm_pos_iff.mpr hx
  have h0 : (0 : ℝ) ∈ s := by
    simp only [s, mem_Ioo]
    constructor <;> linarith
  have hsOpen : IsOpen s := by dsimp [s]; exact isOpen_Ioo
  have hsConvex : Convex ℝ s := by dsimp [s]; exact convex_Ioo _ _
  have hqpos : ∀ t ∈ s, q t ≠ 0 := by
    intro t ht
    have htAbs  := abs_lt.mpr ⟨ht.1, ht.2⟩
    have hnormLower : ‖x‖ - |t| ≤ ‖x + (t : ℂ)‖ := by
      have h := norm_sub_norm_le x (-(t : ℂ))
      simp_all
    have hpositive : 0 < ‖x + (t : ℂ)‖ := by
      have : 0 < ‖x‖ - |t| := by dsimp [ρ] at htAbs; linarith
      exact lt_of_lt_of_le this hnormLower
    have hqeq : q t = ‖x + (t : ℂ)‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← radialShiftSq_eq_normSq]
    rw [hqeq]
    positivity
  have hqCont : ContDiff ℝ 2 q := by
    change ContDiff ℝ 2
      (fun t : ℝ => ‖x‖ ^ 2 + x.re * t * 2 + t ^ 2)
    fun_prop
  have hcontQ : ContDiffOn ℝ 2 (fun t => q t ^ (k / 2)) s :=
    hqCont.contDiffOn.rpow_const_of_ne (fun t ht => hqpos t ht)
  have hfun : f = fun t => q t ^ (k / 2) := by
    funext t
    dsimp [f, q]
    rw [norm_rpow_eq_norm_sq_rpow, ← Complex.normSq_eq_norm_sq,
      radialShiftSq_eq_normSq]
  have hf : ContDiffOn ℝ 2 f s := by rwa [hfun]
  have hlimit := central_second_difference_tendsto hsConvex hsOpen h0 hf
  have hsecond := hasDerivAt_deriv_norm_rpow_shift k x hx
  have hsecondVal := hsecond.deriv
  rw [hsecondVal] at hlimit
  simpa [f, sub_eq_add_neg] using hlimit

/-- Quarter rotation gives the imaginary second difference from the real one. -/
theorem norm_rpow_imag_centered_difference_tendsto :
    Tendsto (fun t : ℝ => radialSecondDiff k x ((t : ℂ) * Complex.I) / t ^ 2)
      (𝓝[≠] (0 : ℝ))
      (𝓝 ((k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) *
          (2 * x.im) ^ 2 + (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2)) := by
  let y := -Complex.I * x
  have hy : y ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hx
  have hn : ‖y‖ = ‖x‖ := by simp [y]
  have hr : y.re = x.im := by simp [y, Complex.mul_re]
  have he (t : ℝ) : radialSecondDiff k y t = radialSecondDiff k x ((t : ℂ) * Complex.I) := by
    have hm : -Complex.I * ((t : ℂ) * Complex.I) = (t : ℂ) := by
      rw [neg_mul, mul_left_comm Complex.I, Complex.I_mul_I]
      ring
    unfold radialSecondDiff
    rw [show y + (t : ℂ) = -Complex.I * (x + (t : ℂ) * Complex.I) by rw [mul_add, hm],
        show y - (t : ℂ) = -Complex.I * (x - (t : ℂ) * Complex.I) by rw [mul_sub, hm], hn]
    simp
  have h := norm_rpow_real_centered_difference_tendsto k y hy
  change Tendsto (fun t : ℝ => radialSecondDiff k y (t : ℂ) / t ^ 2) _ _ at h
  simpa only [he, hn, hr] using h

/-- The discrete Laplacian is the sum of the two centered second derivatives. -/
theorem norm_rpow_discrete_laplacian_tendsto :
    Tendsto (fun t : ℝ => normPowerDiscreteLaplacian k t x)
      (𝓝[≠] (0 : ℝ)) (𝓝 (k ^ 2 * ‖x‖ ^ (k - 2))) := by
  simpa only [normPowerDiscreteLaplacian_eq, normPowerRealSecondDifference, radialSecondDiff,
    radial_rpow_laplacian_coefficient k x hx] using
    (norm_rpow_real_centered_difference_tendsto k x hx).add
      (norm_rpow_imag_centered_difference_tendsto k x hx)

end

end DOZZ.Proofs
