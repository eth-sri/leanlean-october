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
      (hasDerivAt_id t).const_mul _
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    convert (hasDerivAt_id t).pow 2 using 1
    · rfl
    · norm_num
  convert (hasDerivAt_const t (‖x‖ ^ 2)).add (hlin.add hsq) using 1
  · ext s
    simp
    ring
  · ring

/-- Derivative of a real power of the squared norm along a coordinate line, away from its zero. -/
theorem hasDerivAt_radialShiftRpow (p : ℝ) (x : ℂ) (t : ℝ)
    (hpos : 0 < radialShiftSq x t) :
    HasDerivAt (fun s : ℝ => radialShiftSq x s ^ p)
      (radialShiftFirstDerivative p x t) t := by
  exact (Real.hasDerivAt_rpow_const
    (Or.inl hpos.ne')).comp t (hasDerivAt_radialShiftSq x t)
section
variable (x : ℂ)

/-- The coordinate formula for the squared norm in `ℂ`. -/
theorem radialShiftSq_eq_normSq (t : ℝ) :
    radialShiftSq x t = Complex.normSq (x + (t : ℂ)) := by
  rw [Complex.normSq_add]
  simp [radialShiftSq, Complex.normSq_ofReal, Complex.mul_re]
  rw [Complex.normSq_eq_norm_sq]
  ring_nf

/-- A norm power is a real power of the squared norm. -/
private theorem norm_rpow_eq_norm_sq_rpow (k : ℝ) :
    ‖x‖ ^ k = (‖x‖ ^ 2) ^ (k / 2) := by
  calc
    ‖x‖ ^ k = ‖x‖ ^ (2 * (k / 2)) := by ring
    _ = (‖x‖ ^ 2) ^ (k / 2) := Real.rpow_natCast_mul (norm_nonneg x) 2 _

end
section
variable (p : ℝ) (x : ℂ)
section
variable (hx : x ≠ 0)
include hx


/-- The derivative of the first derivative of `‖x + t‖^(2p)` at `t=0`, for `x ≠ 0`.
This is the one-dimensional second-derivative calculation used away from the collision point. -/
theorem hasDerivAt_radialShiftFirstDerivative :
    HasDerivAt (radialShiftFirstDerivative p x)
      (p * (p - 1) * (‖x‖ ^ 2) ^ (p - 2) * (2 * x.re) ^ 2 +
        p * (‖x‖ ^ 2) ^ (p - 1) * 2) 0 := by
  let q := radialShiftSq x
  have hq : HasDerivAt q (2 * x.re) 0 := by
    change HasDerivAt (fun t : ℝ => ‖x‖ ^ 2 + x.re * t * 2 + t ^ 2) _ _
    have hlin : HasDerivAt (fun t : ℝ => x.re * t * 2) (2 * x.re) 0 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (hasDerivAt_id 0).const_mul (2 * x.re)
    have hsq : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
      convert (hasDerivAt_id (0 : ℝ)).pow 2 using 1
      · rfl
      · norm_num
    convert (hasDerivAt_const 0 (‖x‖ ^ 2)).add (hlin.add hsq)
      using 1
    · ext t
      simp
      ring
    · ring
  have hq0 : q 0 = ‖x‖ ^ 2 := by simp [q, radialShiftSq]
  have hqpos : 0 < q 0 := by simp_all
  have hpow : HasDerivAt (fun t => q t ^ (p - 1))
      ((p - 1) * q 0 ^ (p - 2) * (2 * x.re)) 0 := by
    convert (Real.hasDerivAt_rpow_const
      (Or.inl hqpos.ne')).comp 0 hq using 1
    · rfl
    ring
  have hlin : HasDerivAt (fun t => 2 * x.re + 2 * t) 2 0 := by
    convert ((hasDerivAt_id 0).const_mul 2).const_add (2 * x.re)
      using 1 <;> norm_num
  have hform : radialShiftFirstDerivative p x =
      fun t => p * q t ^ (p - 1) * (2 * x.re + 2 * t) := by
    rfl
  rw [hform]
  convert ((hpow.mul hlin).const_mul p) using 1
  · ext t
    simp
    ring
  grind

/-- The second derivative of a radial power along a real coordinate line, at its nonzero center. -/
theorem hasDerivAt_deriv_radialShiftRpow :
    HasDerivAt (fun t : ℝ => deriv (fun s => radialShiftSq x s ^ p) t)
      (p * (p - 1) * (‖x‖ ^ 2) ^ (p - 2) * (2 * x.re) ^ 2 +
        p * (‖x‖ ^ 2) ^ (p - 1) * 2) 0 := by
  let q := radialShiftSq x
  have hq0 : q 0 = ‖x‖ ^ 2 := by simp [q, radialShiftSq]
  have hqpos : 0 < q 0 := by simp_all
  have hqcont : Continuous q := by
    change Continuous (fun t : ℝ => ‖x‖ ^ 2 + x.re * t * 2 + t ^ 2)
    fun_prop
  have hqposEv :=
    hqcont.continuousAt.eventually (isOpen_Ioi.mem_nhds hqpos)
  have hderivEq : deriv (fun s => q s ^ p) =ᶠ[𝓝 0]
      radialShiftFirstDerivative p x := by
    filter_upwards [hqposEv] with t ht
    exact (hasDerivAt_radialShiftRpow p x t ht).deriv
  exact (hasDerivAt_radialShiftFirstDerivative p x hx).congr_of_eventuallyEq hderivEq

end

end
section
variable (k : ℝ)
section
variable (x : ℂ)
section
variable (hx : x ≠ 0)
include hx

/-- The second derivative of `‖x+t‖^k` at `t=0`, written through the squared norm. -/
theorem hasDerivAt_deriv_norm_rpow_shift :
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ => ‖x + (s : ℂ)‖ ^ k) t)
      ((k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) *
          (2 * x.re) ^ 2 +
        (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2) 0 := by
  have hfun : (fun t : ℝ => ‖x + t‖ ^ k) =
      (fun t => radialShiftSq x t ^ (k / 2)) := by
    funext t
    rw [norm_rpow_eq_norm_sq_rpow, ← Complex.normSq_eq_norm_sq, radialShiftSq_eq_normSq]
  have hderiv : (fun t : ℝ => deriv (fun s : ℝ => ‖x + s‖ ^ k) t) =
      (fun t => deriv (fun s : ℝ => radialShiftSq x s ^ (k / 2)) t) := by
    simp_all
  have hsecond := hasDerivAt_deriv_radialShiftRpow (k / 2) x hx
  simp_all


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
  let p := k / 2
  let r := ‖x‖ ^ 2
  have hr : 0 < r := by
    positivity
  have hcoord : (2 * x.re) ^ 2 + (2 * x.im) ^ 2 = 4 * r := by
    dsimp [r]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hpow : r ^ (p - 2) * r = r ^ (p - 1) := by
    calc
      r ^ (p - 2) * r = r ^ (p - 2) * r ^ 1 := by simp
      _ = r ^ ((p - 2) + 1) := (Real.rpow_add hr _ 1).symm
      _ = r ^ (p - 1) := by ring
  have hnormpow : r ^ (p - 1) = ‖x‖ ^ (k - 2) := by
    dsimp [p, r]
    rw [show k / 2 - 1 = (k - 2) / 2 by ring]
    exact (norm_rpow_eq_norm_sq_rpow x _).symm
  grind

end

end
section
variable (hk : 0 < k) (hk₂ : k < 2)
include hk hk₂
section
variable (x y : ℂ) (hx : x ≠ 0)
include hx

/-- A centered second difference of a radial power is quadratically bounded when the
increment is at most half the distance to the origin. -/
theorem norm_rpow_centered_difference_le (hy : ‖y‖ ≤ ‖x‖ / 2) :
    |‖x + y‖ ^ k + ‖x - y‖ ^ k - 2 * ‖x‖ ^ k| ≤
      (2 * (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2))))) *
        ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by
  let q := y / x
  let C := k * (1 + (15 / 4) *
    ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hqnorm : ‖q‖ = ‖y‖ / ‖x‖ := by aesop
  have hq : ‖q‖ ≤ 1 / 2 := by
    rw [hqnorm]
    apply (div_le_iff₀ hxpos).2
    linarith
  have hplus : x + y = x * (1 + q) := by
    grind
  have hminus : x - y = x * (1 - q) := by
    grind
  have hplusPow : ‖x + y‖ ^ k = ‖x‖ ^ k * ‖1 + q‖ ^ k := by
    rw [hplus, norm_mul, Real.mul_rpow (norm_nonneg x) (norm_nonneg (1 + q))]
  have hminusPow : ‖x - y‖ ^ k = ‖x‖ ^ k * ‖1 - q‖ ^ k := by
    rw [hminus, norm_mul, Real.mul_rpow (norm_nonneg x) (norm_nonneg (1 - q))]
  have hremPlus := norm_unit_taylor_remainder_le k hk hk₂ (-q) (by simp_all)
  have hC : 0 ≤ C := by
    dsimp [C]
    have hfactor : 0 ≤ 1 - k / 2 := by linarith
    positivity
  have hCnorm : |‖1 - q‖ ^ k - 1 + k * q.re| ≤ C * ‖q‖ ^ 2 := by
    simpa [C] using (norm_unit_taylor_remainder_le k hk hk₂ q hq)
  have hCnorm' : |‖1 + q‖ ^ k - 1 - k * q.re| ≤ C * ‖q‖ ^ 2 := by
    calc
      |‖1 + q‖ ^ k - 1 - k * q.re| =
          |‖1 - -q‖ ^ k - 1 + k * (-q).re| := by
            congr 1
            simp
            ring
      _ ≤ C * ‖-q‖ ^ 2 := by assumption
      _ = C * ‖q‖ ^ 2 := by simp
  have hpair : ‖x + y‖ ^ k + ‖x - y‖ ^ k - 2 * ‖x‖ ^ k =
      ‖x‖ ^ k * ((‖1 + q‖ ^ k - 1 - k * q.re) +
        (‖1 - q‖ ^ k - 1 + k * q.re)) := by
    rw [hplusPow, hminusPow]
    ring
  have hnormx : 0 ≤ ‖x‖ ^ k := by positivity
  calc
    _ = ‖x‖ ^ k * |(‖1 + q‖ ^ k - 1 - k * q.re) +
          (‖1 - q‖ ^ k - 1 + k * q.re)| := by
            rw [hpair, abs_mul, abs_of_nonneg hnormx]
    _ ≤ ‖x‖ ^ k * (|‖1 + q‖ ^ k - 1 - k * q.re| +
          |‖1 - q‖ ^ k - 1 + k * q.re|) :=
            mul_le_mul_of_nonneg_left (abs_add_le ..) hnormx
    _ ≤ ‖x‖ ^ k * (C * ‖q‖ ^ 2 + C * ‖q‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hCnorm' hCnorm) hnormx
    _ = (2 * C) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by
          rw [hqnorm, div_pow]
          have hpow : ‖x‖ ^ k / ‖x‖ ^ (2 : ℝ) = ‖x‖ ^ (k - 2) :=
            (Real.rpow_sub hxpos k 2).symm
          rw [← Real.rpow_natCast ‖x‖ 2]
          calc
            ‖x‖ ^ k * (C * (‖y‖ ^ 2 / ‖x‖ ^ (2 : ℝ)) +
                C * (‖y‖ ^ 2 / ‖x‖ ^ (2 : ℝ))) =
                2 * C * ‖y‖ ^ 2 * (‖x‖ ^ k / ‖x‖ ^ (2 : ℝ)) := by ring
            _ = (2 * C) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by simp_all

/-- A global second-difference majorant, including increments that reach or cross the origin.
The constant is deliberately explicit so it can be used under an integral. -/
theorem norm_rpow_centered_difference_le_global :
    |‖x + y‖ ^ k + ‖x - y‖ ^ k - 2 * ‖x‖ ^ k| ≤
      (2 * (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) +
        2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k)) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by
  let C := k * (1 + (15 / 4) *
    ((1 - k / 2) * (1 / 4) ^ (k / 2 - 2)))
  let B : ℝ := 2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k)
  have hxpos := norm_pos_iff.mpr hx
  have hC : 0 ≤ C := by
    bound
  have hB : 0 ≤ B := by
    positivity
  by_cases hsmall : ‖y‖ ≤ ‖x‖ / 2
  · have hlocal := norm_rpow_centered_difference_le k hk hk₂ x y hx hsmall
    have hweight : 0 ≤ ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by positivity
    change |‖x + y‖ ^ k + ‖x - y‖ ^ k - 2 * ‖x‖ ^ k| ≤
      (2 * C + B) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2)
    calc
      _ ≤ 2 * C * (‖y‖ ^ 2 * ‖x‖ ^ (k - 2)) := by
        grind
      _ ≤ (2 * C + B) * (‖y‖ ^ 2 * ‖x‖ ^ (k - 2)) := by nlinarith
      _ = (2 * C + B) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by ring
  · have hlarge := lt_of_not_ge hsmall
    have hypos := lt_of_le_of_lt (by positivity) hlarge
    have hxle : ‖x‖ ≤ 2 * ‖y‖ := by linarith
    have hplus : ‖x + y‖ ≤ 3 * ‖y‖ := by
      calc
        ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le ..
        _ ≤ 3 * ‖y‖ := by linarith
    have hminus : ‖x - y‖ ≤ 3 * ‖y‖ := by
      calc
        ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le ..
        _ ≤ 3 * ‖y‖ := by linarith
    have hplusPow :=
      Real.rpow_le_rpow (norm_nonneg _) hplus hk.le
    have hminusPow :=
      Real.rpow_le_rpow (norm_nonneg _) hminus hk.le
    have hxPow :=
      Real.rpow_le_rpow (norm_nonneg _) hxle hk.le
    have hraw : |‖x + y‖ ^ k + ‖x - y‖ ^ k - 2 * ‖x‖ ^ k| ≤
        2 * (3 * ‖y‖) ^ k + 2 * (2 * ‖y‖) ^ k := by
      calc
        _ ≤ |‖x + y‖ ^ k + ‖x - y‖ ^ k| + |2 * ‖x‖ ^ k| := abs_sub ..
        _ = ‖x + y‖ ^ k + ‖x - y‖ ^ k + 2 * ‖x‖ ^ k := by
          rw [abs_of_nonneg (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
            (Real.rpow_nonneg (norm_nonneg _) _)), abs_of_nonneg (by positivity)]
        _ ≤ 2 * (3 * ‖y‖) ^ k + 2 * (2 * ‖y‖) ^ k := by
          linarith only [hplusPow, hminusPow, hxPow]
    have hmul3 : (3 * ‖y‖) ^ k = 3 ^ k * ‖y‖ ^ k :=
      Real.mul_rpow (by norm_num) (norm_nonneg y)
    have hmul2 : (2 * ‖y‖) ^ k = 2 ^ k * ‖y‖ ^ k :=
      Real.mul_rpow (by norm_num) (norm_nonneg y)
    have hySplit : ‖y‖ ^ k = ‖y‖ ^ 2 * ‖y‖ ^ (k - 2) := by
      calc
        ‖y‖ ^ k = ‖y‖ ^ (2 + (k - 2)) := by simp
        _ = ‖y‖ ^ 2 * ‖y‖ ^ (k - 2) := Real.rpow_add hypos ..
        _ = ‖y‖ ^ 2 * ‖y‖ ^ (k - 2) :=
          congrArg (fun t => t * ‖y‖ ^ (k - 2)) (Real.rpow_natCast ‖y‖ 2)
    have hhalf : (‖x‖ / 2) ^ (k - 2) =
        2 ^ (2 - k) * ‖x‖ ^ (k - 2) := by
      rw [show ‖x‖ / 2 = ‖x‖ * (1 / 2) by ring,
        Real.mul_rpow (norm_nonneg x) (by norm_num : 0 ≤ (1 / 2 : ℝ)),
        show (1 / 2 : ℝ) ^ (k - 2) = 2 ^ (2 - k) by
          rw [show (1 / 2) = (2 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num)]
          rw [show 2 - k = -(k - 2) by ring,
            ← Real.rpow_neg (by norm_num)]]
      ring
    have hnegative : k - 2 ≤ 0 := by linarith
    have hdecrease : ‖y‖ ^ (k - 2) ≤ (‖x‖ / 2) ^ (k - 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hnegative
    have hyBound : ‖y‖ ^ k ≤
        ‖y‖ ^ 2 * (2 ^ (2 - k) * ‖x‖ ^ (k - 2)) := by
      rw [hySplit]
      exact mul_le_mul_of_nonneg_left (hdecrease.trans_eq hhalf) (sq_nonneg ‖y‖)
    change |‖x + y‖ ^ k + ‖x - y‖ ^ k - 2 * ‖x‖ ^ k| ≤
      (2 * C + B) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2)
    calc
      _ ≤ 2 * (3 * ‖y‖) ^ k + 2 * (2 * ‖y‖) ^ k := hraw
      _ = 2 * (3 ^ k + 2 ^ k) * ‖y‖ ^ k := by linarith
      _ ≤ B * (‖y‖ ^ 2 * ‖x‖ ^ (k - 2)) := by
        calc
          2 * (3 ^ k + 2 ^ k) * ‖y‖ ^ k ≤
              2 * (3 ^ k + 2 ^ k) *
                (‖y‖ ^ 2 * (2 ^ (2 - k) * ‖x‖ ^ (k - 2))) :=
            mul_le_mul_of_nonneg_left hyBound (by positivity)
          _ = B * (‖y‖ ^ 2 * ‖x‖ ^ (k - 2)) := by linarith
      _ ≤ (2 * C + B) * (‖y‖ ^ 2 * ‖x‖ ^ (k - 2)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (2 * C + B) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by ring

end

/-- The four-direction discrete Laplacian is dominated by the positive radial kernel, uniformly
in every nonzero step. -/
theorem norm_rpow_discrete_laplacian_le (x : ℂ) (t : ℝ) (hx : x ≠ 0) (ht : t ≠ 0) :
    |(‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k +
      ‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k -
      4 * ‖x‖ ^ k) / t ^ 2| ≤
      (2 * (2 * (k * (1 + (15 / 4) *
        ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) +
        2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k))) * ‖x‖ ^ (k - 2) := by
  let C : ℝ := 2 * (k * (1 + (15 / 4) *
    ((1 - k / 2) * (1 / 4) ^ (k / 2 - 2)))) +
    2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k)
  have hR := norm_rpow_centered_difference_le_global k hk hk₂ x t hx
  have hI := norm_rpow_centered_difference_le_global k hk hk₂ x
    (t * Complex.I) hx
  have hR' : |‖x + t‖ ^ k + ‖x - t‖ ^ k - 2 * ‖x‖ ^ k| ≤
      C * t ^ 2 * ‖x‖ ^ (k - 2) := by
    aesop
  have hI' : |‖x + t * Complex.I‖ ^ k +
      ‖x - t * Complex.I‖ ^ k - 2 * ‖x‖ ^ k| ≤
      C * t ^ 2 * ‖x‖ ^ (k - 2) := by
    aesop
  have hsum :
      |(‖x + t‖ ^ k + ‖x - t‖ ^ k - 2 * ‖x‖ ^ k) +
        (‖x + t * Complex.I‖ ^ k + ‖x - t * Complex.I‖ ^ k -
          2 * ‖x‖ ^ k)| ≤ 2 * C * t ^ 2 * ‖x‖ ^ (k - 2) := by
    grind
  have ht2 := sq_pos_of_ne_zero ht
  have hnum :
      ‖x + t‖ ^ k + ‖x - t‖ ^ k +
        ‖x + t * Complex.I‖ ^ k + ‖x - t * Complex.I‖ ^ k -
        4 * ‖x‖ ^ k =
      (‖x + t‖ ^ k + ‖x - t‖ ^ k - 2 * ‖x‖ ^ k) +
        (‖x + t * Complex.I‖ ^ k + ‖x - t * Complex.I‖ ^ k -
          2 * ‖x‖ ^ k) := by ring
  rw [hnum, abs_div, abs_of_pos ht2]
  apply (div_le_iff₀ ht2).2
  calc
    |(‖x + t‖ ^ k + ‖x - t‖ ^ k - 2 * ‖x‖ ^ k) +
        (‖x + t * Complex.I‖ ^ k + ‖x - t * Complex.I‖ ^ k -
          2 * ‖x‖ ^ k)| ≤ 2 * C * t ^ 2 * ‖x‖ ^ (k - 2) := hsum
    _ = (2 * C * ‖x‖ ^ (k - 2)) * t ^ 2 := by ring

end

end

/-- Explicit second-order Taylor polynomial at an interior point of an open interval. -/
theorem taylorWithinEval_two_eq (f : ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s)
    (h0 : (0 : ℝ) ∈ s) (t : ℝ) (_ht : t ∈ s) :
    taylorWithinEval f 2 s 0 t =
      f 0 + t * deriv f 0 + (t ^ 2 / 2) * deriv (deriv f) 0 := by
  have h1 : iteratedDerivWithin 1 f s 0 = deriv f 0 := by
    exact iteratedDerivWithin_of_isOpen_eq_iterate hs h0
  have h2 : iteratedDerivWithin 2 f s 0 = deriv (deriv f) 0 := by
    exact iteratedDerivWithin_of_isOpen_eq_iterate hs h0
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
  let P : ℝ → ℝ := fun t => taylorWithinEval f 2 s 0 t
  have hsNhds := hso.mem_nhds h0
  have hTaylor : Tendsto (fun t : ℝ => (f t - P t) / t ^ 2)
      (𝓝 0) (𝓝 0) := by
    have h := Real.taylor_tendsto (f := f) (x₀ := 0) (s := s) hs h0 hf
    rw [hso.nhdsWithin_eq h0] at h
    aesop
  have hid : Tendsto (fun t : ℝ => t) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[≠] 0) (𝓝 0) := by
    simpa using hid.neg
  have hnegErr : Tendsto (fun t : ℝ => (f (-t) - P (-t)) / t ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
    convert hTaylor.comp hneg using 1
    grind
  have hsum : Tendsto
      (fun t : ℝ => (deriv (deriv f) 0) +
        ((f t - P t) / t ^ 2 + (f (-t) - P (-t)) / t ^ 2))
      (𝓝[≠] 0) (𝓝 (deriv (deriv f) 0)) := by
    simpa [add_assoc] using tendsto_const_nhds.add ((hTaylor.comp hid).add hnegErr)
  have hne : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using ht
  have hmem : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), t ∈ s ∧ -t ∈ s := by
    filter_upwards [hid.eventually hsNhds, hneg.eventually hsNhds] with t ht₁ ht₂
    change t ∈ s at ht₁
    change -t ∈ s at ht₂
    exact ⟨ht₁, ht₂⟩
  have heq : (fun t : ℝ => (f t + f (-t) - 2 * f 0) / t ^ 2) =ᶠ[𝓝[≠] 0]
      fun t => (deriv (deriv f) 0) +
        ((f t - P t) / t ^ 2 + (f (-t) - P (-t)) / t ^ 2) := by
    filter_upwards [hne, hmem] with t ht hmem
    obtain ⟨hts, hnts⟩ := hmem
    dsimp [P]
    rw [(taylorWithinEval_two_eq f s hso h0 t hts), (taylorWithinEval_two_eq f s hso h0 (-t) hnts)]
    field_simp [ht]
    ring
  exact hsum.congr' heq.symm
section
variable (k : ℝ) (x : ℂ)
section
variable (hx : x ≠ 0)
include hx

/-- The real-coordinate centered difference of `‖x+t‖^k` converges to its second derivative
at every nonzero center. -/
theorem norm_rpow_real_centered_difference_tendsto :
    Tendsto (fun t : ℝ =>
      (‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k - 2 * ‖x‖ ^ k) / t ^ 2)
      (𝓝[≠] (0 : ℝ))
      (𝓝 ((k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) *
          (2 * x.re) ^ 2 + (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2)) := by
  let ρ := ‖x‖ / 2
  let s := Ioo (-ρ) ρ
  let f : ℝ → ℝ := fun t => ‖x + (t : ℂ)‖ ^ k
  let q := radialShiftSq x
  have hρ : 0 < ρ := by positivity
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h0 : (0 : ℝ) ∈ s := by
    aesop
  have hsOpen : IsOpen s := by dsimp [s]; exact isOpen_Ioo
  have hsConvex : Convex ℝ s := by dsimp [s]; exact convex_Ioo ..
  have hqpos : ∀ t ∈ s, q t ≠ 0 := by
    intro t ht
    have htAbs : |t| < ρ := by grind
    have hnormLower : ‖x‖ - |t| ≤ ‖x + (t : ℂ)‖ := by
      have h := norm_sub_norm_le x (-(t : ℂ))
      simp_all
    have hpositive : 0 < ‖x + (t : ℂ)‖ := by
      grind
    have hqeq : q t = ‖x + (t : ℂ)‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← radialShiftSq_eq_normSq]
    rw [hqeq]
    positivity
  have hqCont : ContDiff ℝ 2 q := by
    change ContDiff ℝ 2
      (fun t => ‖x‖ ^ 2 + x.re * t * 2 + t ^ 2)
    fun_prop
  have hcontQ : ContDiffOn ℝ 2 (fun t => q t ^ (k / 2)) s :=
    by fun_prop
  have hfun : f = fun t => q t ^ (k / 2) := by
    funext t
    dsimp [f, q]
    rw [norm_rpow_eq_norm_sq_rpow, ← Complex.normSq_eq_norm_sq,
      radialShiftSq_eq_normSq]
  have hf : ContDiffOn ℝ 2 f s := by simp_all
  have hlimit := central_second_difference_tendsto hsConvex hsOpen h0 hf
  have hsecondVal : deriv (deriv f) 0 =
      (k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) *
        (2 * x.re) ^ 2 + (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2 := by
    exact (hasDerivAt_deriv_norm_rpow_shift k x hx).deriv
  rw [hsecondVal] at hlimit
  simpa [f, sub_eq_add_neg] using hlimit

/-- The imaginary-coordinate centered difference has the corresponding second derivative
limit. -/
theorem norm_rpow_imag_centered_difference_tendsto :
    Tendsto (fun t : ℝ =>
      (‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k -
        2 * ‖x‖ ^ k) / t ^ 2)
      (𝓝[≠] (0 : ℝ))
      (𝓝 ((k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) *
          (2 * x.im) ^ 2 + (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2)) := by
  let y := -Complex.I * x
  have hy : y ≠ 0 := by
    aesop
  have hnorm : ‖y‖ = ‖x‖ := by
    aesop
  have hRe : y.re = x.im := by
    aesop
  have hplus : ∀ t : ℝ, ‖x + t * Complex.I‖ = ‖y + t‖ := by
    intro t
    have hm : (-Complex.I) * (x + t * Complex.I) = y + t := by
      rw [mul_add]
      congr 1
      calc
        (-Complex.I) * (t * Complex.I) = -(t * (Complex.I * Complex.I)) := by
          ring
        _ = t := by simp
    calc
      ‖x + t * Complex.I‖ =
          ‖(-Complex.I) * (x + t * Complex.I)‖ := by simp
      _ = ‖y + t‖ := by simp_all
  have hminus : ∀ t : ℝ, ‖x - t * Complex.I‖ = ‖y - t‖ := by
    intro t
    have hm : (-Complex.I) * (x - t * Complex.I) = y - t := by
      rw [mul_sub]
      congr 1
      calc
        (-Complex.I) * (t * Complex.I) = -(t * (Complex.I * Complex.I)) := by
          ring
        _ = t := by simp
    calc
      ‖x - t * Complex.I‖ =
          ‖(-Complex.I) * (x - t * Complex.I)‖ := by simp
      _ = ‖y - t‖ := by simp_all
  have hreal := norm_rpow_real_centered_difference_tendsto k y hy
  simp_all

/-- The symmetric four-direction discrete Laplacian of a radial power converges to its
planar Laplacian away from the origin. -/
theorem norm_rpow_discrete_laplacian_tendsto :
    Tendsto (fun t : ℝ =>
      (‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k +
        ‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k -
        4 * ‖x‖ ^ k) / t ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (k ^ 2 * ‖x‖ ^ (k - 2))) := by
  let dRe := (k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) *
    (2 * x.re) ^ 2 + (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2
  let dIm := (k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) *
    (2 * x.im) ^ 2 + (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2
  have hsum : Tendsto
      (fun t : ℝ =>
        (‖x + t‖ ^ k + ‖x - t‖ ^ k - 2 * ‖x‖ ^ k) / t ^ 2 +
        (‖x + t * Complex.I‖ ^ k + ‖x - t * Complex.I‖ ^ k -
          2 * ‖x‖ ^ k) / t ^ 2)
      (𝓝[≠] 0) (𝓝 (dRe + dIm)) := by
    simpa [dRe, dIm] using (norm_rpow_real_centered_difference_tendsto k x hx).add (norm_rpow_imag_centered_difference_tendsto k x hx)
  have hEq : (fun t : ℝ =>
      (‖x + t‖ ^ k + ‖x - t‖ ^ k +
        ‖x + t * Complex.I‖ ^ k + ‖x - t * Complex.I‖ ^ k -
        4 * ‖x‖ ^ k) / t ^ 2) =ᶠ[𝓝[≠] 0]
      fun t =>
        (‖x + t‖ ^ k + ‖x - t‖ ^ k - 2 * ‖x‖ ^ k) / t ^ 2 +
        (‖x + t * Complex.I‖ ^ k + ‖x - t * Complex.I‖ ^ k -
          2 * ‖x‖ ^ k) / t ^ 2 := by
    filter_upwards [] with t
    ring
  rw [show dRe + dIm = k ^ 2 * ‖x‖ ^ (k - 2) from (radial_rpow_laplacian_coefficient k x hx)] at hsum
  exact hsum.congr' hEq.symm

end

end

end DOZZ.Proofs
