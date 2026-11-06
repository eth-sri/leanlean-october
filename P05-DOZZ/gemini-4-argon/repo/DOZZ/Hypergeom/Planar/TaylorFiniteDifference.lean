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



/-- The coordinate formula for the squared norm in `ℂ`. -/
theorem radialShiftSq_eq_normSq x (t : ℝ) :
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








/-- A global second-difference majorant, including increments that reach or cross the origin.
The constant is deliberately explicit so it can be used under an integral. -/
theorem norm_rpow_centered_difference_le_global (k : ℝ) (hk : 0 < k) (hk₂ : k < 2)
    (x y : ℂ) (hx : x ≠ 0) :
    |‖x + y‖ ^ k + ‖x - y‖ ^ k - 2 * ‖x‖ ^ k| ≤
      (2 * (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) +
        2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k)) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by
  have norm_rpow_centered_difference_le (hy : ‖y‖ ≤ ‖x‖ / 2) : |‖x + y‖ ^ k + ‖x - y‖ ^ k - 2 * ‖x‖ ^ k| ≤ (2 * (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2))))) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by
    let q := y / x
    let C := k * (1 + (15 / 4) *
      ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))
    have hxpos := norm_pos_iff.mpr hx
    have hqnorm : ‖q‖ = ‖y‖ / ‖x‖ := by simp [q]
    have hq : ‖q‖ ≤ 1 / 2 := by
      rw [hqnorm]
      apply (div_le_iff₀ hxpos).2
      nlinarith [hy]
    have hCnorm' : |‖1 + q‖ ^ k - 1 - k * q.re| ≤ C * ‖q‖ ^ 2 := by
      calc
        |‖1 + q‖ ^ k - 1 - k * q.re| =
            |‖1 - -q‖ ^ k - 1 + k * (-q).re| := by
              congr 1
              simp only [sub_neg_eq_add, Complex.neg_re]
              ring
        _ ≤ C * ‖-q‖ ^ 2 := by simpa [C] using (norm_unit_taylor_remainder_le k hk hk₂ (-q) (by simpa using hq))
        _ = C * ‖q‖ ^ 2 := by simp
    have hnormx := Real.rpow_nonneg (norm_nonneg x) k
    calc
      _ = ‖x‖ ^ k * |(‖1 + q‖ ^ k - 1 - k * q.re) +
            (‖1 - q‖ ^ k - 1 + k * q.re)| := by
              rw [(show ‖x + y‖ ^ k + ‖x - y‖ ^ k - 2 * ‖x‖ ^ k = ‖x‖ ^ k * ((‖1 + q‖ ^ k - 1 - k * q.re) + (‖1 - q‖ ^ k - 1 + k * q.re)) by rw [(show ‖x + y‖ ^ k = ‖x‖ ^ k * ‖1 + q‖ ^ k by rw [(show x + y = x * (1 + q) by dsimp [q]; field_simp [hx]), norm_mul, Real.mul_rpow (norm_nonneg x) (norm_nonneg (1 + q))]), (show ‖x - y‖ ^ k = ‖x‖ ^ k * ‖1 - q‖ ^ k by rw [(show x - y = x * (1 - q) by dsimp [q]; field_simp [hx]), norm_mul, Real.mul_rpow (norm_nonneg x) (norm_nonneg (1 - q))])]; ring), abs_mul, abs_of_nonneg hnormx]
      _ ≤ ‖x‖ ^ k * (|‖1 + q‖ ^ k - 1 - k * q.re| +
            |‖1 - q‖ ^ k - 1 + k * q.re|) :=
              mul_le_mul_of_nonneg_left (abs_add_le _ _) hnormx
      _ ≤ ‖x‖ ^ k * (C * ‖q‖ ^ 2 + C * ‖q‖ ^ 2) := by
            exact mul_le_mul_of_nonneg_left (add_le_add hCnorm' (by simpa [C] using (norm_unit_taylor_remainder_le k hk hk₂ q hq))) hnormx
      _ = (2 * C) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by
            rw [hqnorm, div_pow, ← Real.rpow_natCast ‖x‖ 2]
            calc
              ‖x‖ ^ k * (C * (‖y‖ ^ 2 / ‖x‖ ^ (2 : ℝ)) +
                  C * (‖y‖ ^ 2 / ‖x‖ ^ (2 : ℝ))) =
                  2 * C * ‖y‖ ^ 2 * (‖x‖ ^ k / ‖x‖ ^ (2 : ℝ)) := by ring
              _ = (2 * C) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by rw [((Real.rpow_sub hxpos k 2).symm)]
  let C : ℝ := k * (1 + (15 / 4) *
    ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))
  let B : ℝ := 2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k)
  have := norm_pos_iff.mpr hx
  have : 0 ≤ C := by
    dsimp [C]
    have hfactor : 0 ≤ 1 - k / 2 := by linarith
    positivity
  have : 0 ≤ B := by
    dsimp [B]
    positivity
  by_cases hsmall : ‖y‖ ≤ ‖x‖ / 2
  · have hlocal := norm_rpow_centered_difference_le hsmall
    change |‖x + y‖ ^ k + ‖x - y‖ ^ k - 2 * ‖x‖ ^ k| ≤
      (2 * C + B) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2)
    calc
      _ ≤ 2 * C * (‖y‖ ^ 2 * ‖x‖ ^ (k - 2)) := by
        simpa [C, mul_assoc] using hlocal
      _ ≤ (2 * C + B) * (‖y‖ ^ 2 * ‖x‖ ^ (k - 2)) := by
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (2 * C + B) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by ring
  · have hlarge : ‖x‖ / 2 < ‖y‖ := lt_of_not_ge hsmall
    have hplus : ‖x + y‖ ≤ 3 * ‖y‖ := by
      calc
        ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
        _ ≤ 3 * ‖y‖ := by linarith
    have hminus : ‖x - y‖ ≤ 3 * ‖y‖ := by
      calc
        ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ 3 * ‖y‖ := by linarith
    have hraw : |‖x + y‖ ^ k + ‖x - y‖ ^ k - 2 * ‖x‖ ^ k| ≤
        2 * (3 * ‖y‖) ^ k + 2 * (2 * ‖y‖) ^ k := by
      calc
        _ ≤ |‖x + y‖ ^ k + ‖x - y‖ ^ k| + |2 * ‖x‖ ^ k| := abs_sub _ _
        _ = ‖x + y‖ ^ k + ‖x - y‖ ^ k + 2 * ‖x‖ ^ k := by
          rw [abs_of_nonneg (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
            (Real.rpow_nonneg (norm_nonneg _) _)), abs_of_nonneg (by positivity)]
        _ ≤ 2 * (3 * ‖y‖) ^ k + 2 * (2 * ‖y‖) ^ k := by
          linarith only [(Real.rpow_le_rpow (norm_nonneg _) hplus hk.le), (Real.rpow_le_rpow (norm_nonneg _) hminus hk.le), (Real.rpow_le_rpow (norm_nonneg _) (by linarith) hk.le : ‖x‖ ^ k ≤ (2 * ‖y‖) ^ k)]
    have hySplit : ‖y‖ ^ k = ‖y‖ ^ 2 * ‖y‖ ^ (k - 2) := by
      calc
        ‖y‖ ^ k = ‖y‖ ^ ((2 : ℝ) + (k - 2)) := by congr 1; ring
        _ = ‖y‖ ^ (2 : ℝ) * ‖y‖ ^ (k - 2) := Real.rpow_add (lt_of_le_of_lt (by positivity) hlarge) _ _
        _ = ‖y‖ ^ 2 * ‖y‖ ^ (k - 2) :=
          congrArg (fun t : ℝ => t * ‖y‖ ^ (k - 2)) (Real.rpow_natCast ‖y‖ 2)
    have hhalf : (‖x‖ / 2) ^ (k - 2) =
        2 ^ (2 - k) * ‖x‖ ^ (k - 2) := by
      rw [show ‖x‖ / 2 = ‖x‖ * (1 / 2 : ℝ) by ring,
        Real.mul_rpow (norm_nonneg x) (by norm_num : 0 ≤ (1 / 2 : ℝ)),
        show (1 / 2 : ℝ) ^ (k - 2) = 2 ^ (2 - k) by
          rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num)]
          rw [show 2 - k = -(k - 2) by ring,
            ← Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ))]]
      ring
    change |‖x + y‖ ^ k + ‖x - y‖ ^ k - 2 * ‖x‖ ^ k| ≤
      (2 * C + B) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2)
    calc
      _ ≤ 2 * (3 * ‖y‖) ^ k + 2 * (2 * ‖y‖) ^ k := hraw
      _ = 2 * (3 ^ k + 2 ^ k) * ‖y‖ ^ k := by rw [(Real.mul_rpow (by norm_num) (norm_nonneg y)), (Real.mul_rpow (by norm_num) (norm_nonneg y))]; ring
      _ ≤ B * (‖y‖ ^ 2 * ‖x‖ ^ (k - 2)) := by
        dsimp [B]
        calc
          2 * (3 ^ k + 2 ^ k) * ‖y‖ ^ k ≤
              2 * (3 ^ k + 2 ^ k) *
                (‖y‖ ^ 2 * (2 ^ (2 - k) * ‖x‖ ^ (k - 2))) :=
            mul_le_mul_of_nonneg_left (by rw [hySplit]; exact mul_le_mul_of_nonneg_left ((Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)).trans_eq hhalf) (sq_nonneg ‖y‖)) (by positivity)
          _ = B * (‖y‖ ^ 2 * ‖x‖ ^ (k - 2)) := by dsimp [B]; ring
      _ ≤ (2 * C + B) * (‖y‖ ^ 2 * ‖x‖ ^ (k - 2)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (2 * C + B) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by ring

/-- The four-direction discrete Laplacian is dominated by the positive radial kernel, uniformly
in every nonzero step. -/
theorem norm_rpow_discrete_laplacian_le (k : ℝ) (hk : 0 < k) (hk₂ : k < 2)
    x (t : ℝ) (hx : x ≠ 0) (ht : t ≠ 0) :
    |(‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k +
      ‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k -
      4 * ‖x‖ ^ k) / t ^ 2| ≤
      (2 * (2 * (k * (1 + (15 / 4) *
        ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) +
        2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k))) * ‖x‖ ^ (k - 2) := by
  let C := 2 * (k * (1 + (15 / 4) *
    ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) +
    2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k)
  have hsum :
      |(‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k - 2 * ‖x‖ ^ k) +
        (‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k -
          2 * ‖x‖ ^ k)| ≤ 2 * C * t ^ 2 * ‖x‖ ^ (k - 2) := by
    calc
      _ ≤ |‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k - 2 * ‖x‖ ^ k| +
          |‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k -
            2 * ‖x‖ ^ k| := abs_add_le _ _
      _ ≤ C * t ^ 2 * ‖x‖ ^ (k - 2) + C * t ^ 2 * ‖x‖ ^ (k - 2) :=
        add_le_add (by simpa [C, Complex.norm_real, Real.norm_eq_abs, sq_abs] using (norm_rpow_centered_difference_le_global k hk hk₂ x (t : ℂ) hx)) (by simpa [C, norm_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs] using (norm_rpow_centered_difference_le_global k hk hk₂ x ((t : ℂ) * Complex.I) hx))
      _ = _ := by ring
  have ht2 := sq_pos_of_ne_zero ht
  rw [(show ‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k + ‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k - 4 * ‖x‖ ^ k = (‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k - 2 * ‖x‖ ^ k) + (‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k - 2 * ‖x‖ ^ k) by ring), abs_div, abs_of_pos ht2]
  apply (div_le_iff₀ ht2).2
  calc
    |(‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k - 2 * ‖x‖ ^ k) +
        (‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k -
          2 * ‖x‖ ^ k)| ≤ 2 * C * t ^ 2 * ‖x‖ ^ (k - 2) := hsum
    _ = (2 * C * ‖x‖ ^ (k - 2)) * t ^ 2 := by ring

/-- Explicit second-order Taylor polynomial at an interior point of an open interval. -/
theorem taylorWithinEval_two_eq (f : ℝ → ℝ) s (hs : IsOpen s)
    (h0 : (0 : ℝ) ∈ s) t (_ht : t ∈ s) :
    taylorWithinEval f 2 s 0 t =
      f 0 + t * deriv f 0 + (t ^ 2 / 2) * deriv (deriv f) 0 := by
  have h1 : iteratedDerivWithin 1 f s 0 = deriv f 0 := by
    simpa [iteratedDeriv_eq_iterate] using (iteratedDerivWithin_of_isOpen_eq_iterate (n := 1) (f := f) hs h0)
  have h2 : iteratedDerivWithin 2 f s 0 = deriv (deriv f) 0 := by
    simpa [iteratedDeriv_eq_iterate] using (iteratedDerivWithin_of_isOpen_eq_iterate (n := 2) (f := f) hs h0)
  simp only [taylorWithinEval_succ, taylor_within_zero_eval, h1, h2,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_zero, Nat.cast_one,
    zero_add, one_mul, inv_one, sub_zero, pow_one]
  ring


/-- The real-coordinate centered difference of `‖x+t‖^k` converges to its second derivative
at every nonzero center. -/
theorem norm_rpow_real_centered_difference_tendsto (k : ℝ) (x : ℂ) (hx : x ≠ 0) :
    Tendsto (fun t : ℝ =>
      (‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k - 2 * ‖x‖ ^ k) / t ^ 2)
      (𝓝[≠] (0 : ℝ))
      (𝓝 ((k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) *
          (2 * x.re) ^ 2 + (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2)) := by
  have central_second_difference_tendsto {f : ℝ → ℝ} {s} (hs : Convex ℝ s) (hso : IsOpen s) (h0 : (0 : ℝ) ∈ s) (hf : ContDiffOn ℝ 2 f s) : Tendsto (fun t : ℝ => (f t + f (-t) - 2 * f 0) / t ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 (deriv (deriv f) 0)) := by
    let P : ℝ → ℝ := fun t => taylorWithinEval f 2 s 0 t
    have hsNhds := hso.mem_nhds h0
    have hTaylor : Tendsto (fun t => (f t - P t) / t ^ 2)
        (𝓝 (0 : ℝ)) (𝓝 0) := by
      have h := Real.taylor_tendsto (f := f) (x₀ := (0 : ℝ)) (s := s) hs h0 hf
      rw [hso.nhdsWithin_eq h0] at h
      simpa [P] using h
    have hid : Tendsto (fun t => t) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    have hneg : Tendsto (fun t => -t) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa using hid.neg
    have hnegErr : Tendsto (fun t => (f (-t) - P (-t)) / t ^ 2)
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      convert hTaylor.comp hneg using 1
      ext t
      simp [P, pow_two]
    have hmem : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), t ∈ s ∧ -t ∈ s := by
      filter_upwards [hid.eventually hsNhds, hneg.eventually hsNhds] with t ht₁ ht₂
      change t ∈ s at ht₁
      change -t ∈ s at ht₂
      exact ⟨ht₁, ht₂⟩
    have heq : (fun t => (f t + f (-t) - 2 * f 0) / t ^ 2) =ᶠ[𝓝[≠] (0 : ℝ)]
        fun t => (deriv (deriv f) 0) +
          ((f t - P t) / t ^ 2 + (f (-t) - P (-t)) / t ^ 2) := by
      filter_upwards [(show ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), t ≠ 0 by filter_upwards [self_mem_nhdsWithin] with t ht; simpa using ht), hmem] with t ht hmem
      obtain ⟨hts, hnts⟩ := hmem
      dsimp [P]
      rw [(taylorWithinEval_two_eq f s hso h0 t hts), (taylorWithinEval_two_eq f s hso h0 (-t) hnts)]
      field_simp [ht]
      ring
    exact (show Tendsto (fun t => (deriv (deriv f) 0) + ((f t - P t) / t ^ 2 + (f (-t) - P (-t)) / t ^ 2)) (𝓝[≠] (0 : ℝ)) (𝓝 (deriv (deriv f) 0)) by simpa [add_assoc] using tendsto_const_nhds.add ((hTaylor.comp hid).add hnegErr)).congr' heq.symm
  have hasDerivAt_deriv_norm_rpow_shift : HasDerivAt (fun t : ℝ => deriv (fun s : ℝ => ‖x + (s : ℂ)‖ ^ k) t) ((k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) * (2 * x.re) ^ 2 + (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2) 0 := by
    have hasDerivAt_deriv_radialShiftRpow p (x : ℂ) (hx : x ≠ 0) : HasDerivAt (fun t : ℝ => deriv (fun s => radialShiftSq x s ^ p) t) (p * (p - 1) * (‖x‖ ^ 2) ^ (p - 2) * (2 * x.re) ^ 2 + p * (‖x‖ ^ 2) ^ (p - 1) * 2) 0 := by
      have hasDerivAt_radialShiftFirstDerivative : HasDerivAt (radialShiftFirstDerivative p x) (p * (p - 1) * (‖x‖ ^ 2) ^ (p - 2) * (2 * x.re) ^ 2 + p * (‖x‖ ^ 2) ^ (p - 1) * 2) 0 := by
        let q := radialShiftSq x
        have hq : HasDerivAt q (2 * x.re) 0 := by
          change HasDerivAt (fun t : ℝ => ‖x‖ ^ 2 + x.re * t * 2 + t ^ 2) _ _
          have hsq : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
            convert (hasDerivAt_id (0 : ℝ)).pow 2 using 1
            · rfl
            · norm_num
          convert (hasDerivAt_const (0 : ℝ) (‖x‖ ^ 2)).add ((show HasDerivAt (fun t : ℝ => x.re * t * 2) (2 * x.re) 0 by simpa [mul_comm, mul_left_comm, mul_assoc] using (hasDerivAt_id (0 : ℝ)).const_mul (2 * x.re)).add hsq)
            using 1
          · ext t
            simp only [Pi.add_apply]
            ring
          · ring
        have hq0 : q 0 = ‖x‖ ^ 2 := by simp [q, radialShiftSq]
        have hpow : HasDerivAt (fun t : ℝ => q t ^ (p - 1))
            ((p - 1) * q 0 ^ (p - 2) * (2 * x.re)) 0 := by
          convert (Real.hasDerivAt_rpow_const (x := q 0) (p := p - 1)
            (Or.inl (show 0 < q 0 by rw [hq0]; positivity).ne')).comp 0 hq using 1
          · rfl
          · rw [show p - 1 - 1 = p - 2 by ring]
        have hlin : HasDerivAt (fun t : ℝ => 2 * x.re + 2 * t) 2 0 := by
          convert ((hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)).const_add (2 * x.re)
            using 1 <;> norm_num
        rw [(show radialShiftFirstDerivative p x = fun t => p * q t ^ (p - 1) * (2 * x.re + 2 * t) by funext t; rfl)]
        convert ((hpow.mul hlin).const_mul p) using 1
        · ext t
          simp only [Pi.mul_apply]
          ring
        · rw [hq0]
          ring
      have hasDerivAt_radialShiftRpow t (hpos : 0 < radialShiftSq x t) : HasDerivAt (fun s : ℝ => radialShiftSq x s ^ p) (radialShiftFirstDerivative p x t) t := by
        have hasDerivAt_radialShiftSq : HasDerivAt (radialShiftSq x) (2 * x.re + 2 * t) t := by
          change HasDerivAt (fun s : ℝ => ‖x‖ ^ 2 + x.re * s * 2 + s ^ 2) _ _
          have hsq : HasDerivAt (fun s => s ^ 2) (2 * t) t := by
            convert (hasDerivAt_id t).pow 2 using 1
            · rfl
            · norm_num
          convert (hasDerivAt_const t (‖x‖ ^ 2)).add ((show HasDerivAt (fun s => x.re * s * 2) (2 * x.re) t by simpa [mul_comm, mul_left_comm, mul_assoc] using (hasDerivAt_id t).const_mul (2 * x.re)).add hsq) using 1
          · ext s
            simp only [Pi.add_apply]
            ring
          · ring
        convert ((Real.hasDerivAt_rpow_const (x := radialShiftSq x t) (p := p) (Or.inl hpos.ne')).comp t (hasDerivAt_radialShiftSq)) using 1 <;> rfl
      let q := radialShiftSq x
      exact (hasDerivAt_radialShiftFirstDerivative).congr_of_eventuallyEq (by filter_upwards [((show Continuous q by change Continuous (fun t => ‖x‖ ^ 2 + x.re * t * 2 + t ^ 2); fun_prop).continuousAt.eventually (isOpen_Ioi.mem_nhds (show 0 < q 0 by rw [(show q 0 = ‖x‖ ^ 2 by simp [q, radialShiftSq])]; positivity)))] with t ht; exact (hasDerivAt_radialShiftRpow t ht).deriv)
    exact (hasDerivAt_deriv_radialShiftRpow (k / 2) x hx).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by rw [(show (fun t : ℝ => ‖x + (t : ℂ)‖ ^ k) = (fun t => radialShiftSq x t ^ (k / 2)) by funext t; rw [norm_rpow_eq_norm_sq_rpow, ← Complex.normSq_eq_norm_sq, radialShiftSq_eq_normSq])]))
  let ρ : ℝ := ‖x‖ / 2
  let s : Set ℝ := Ioo (-ρ) ρ
  let f : ℝ → ℝ := fun t => ‖x + (t : ℂ)‖ ^ k
  let q : ℝ → ℝ := radialShiftSq x
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hxpos := norm_pos_iff.mpr hx
  have hqpos : ∀ t ∈ s, q t ≠ 0 := by
    intro t ht
    have htAbs := abs_lt.mpr ⟨ht.1, ht.2⟩
    have hnormLower : ‖x‖ - |t| ≤ ‖x + (t : ℂ)‖ := by
      have h := norm_sub_norm_le x (-(t : ℂ))
      rw [(show ‖-(t : ℂ)‖ = |t| by rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]), (show x - -(t : ℂ) = x + (t : ℂ) by ring)] at h
      exact h
    have : 0 < ‖x + (t : ℂ)‖ := by
      have : 0 < ‖x‖ - |t| := by dsimp [ρ] at htAbs; linarith
      exact lt_of_lt_of_le this hnormLower
    rw [(show q t = ‖x + (t : ℂ)‖ ^ 2 by rw [← Complex.normSq_eq_norm_sq, ← radialShiftSq_eq_normSq])]
    positivity
  have hfun : f = fun t => q t ^ (k / 2) := by
    funext t
    dsimp [f, q]
    rw [norm_rpow_eq_norm_sq_rpow, ← Complex.normSq_eq_norm_sq,
      radialShiftSq_eq_normSq]
  have hf : ContDiffOn ℝ 2 f s := by rw [hfun]; exact ((show ContDiff ℝ 2 q by change ContDiff ℝ 2 (fun t : ℝ => ‖x‖ ^ 2 + x.re * t * 2 + t ^ 2); fun_prop).contDiffOn.rpow_const_of_ne (fun t ht => hqpos t ht))
  have hlimit := central_second_difference_tendsto (by dsimp [s]; exact convex_Ioo _ _) (by dsimp [s]; exact isOpen_Ioo) (show (0 : ℝ) ∈ s by simp only [s, mem_Ioo]; constructor <;> linarith) hf
  rw [((hasDerivAt_deriv_norm_rpow_shift).deriv)] at hlimit
  simpa [f, sub_eq_add_neg] using hlimit


/-- The symmetric four-direction discrete Laplacian of a radial power converges to its
planar Laplacian away from the origin. -/
theorem norm_rpow_discrete_laplacian_tendsto k x (hx : x ≠ 0) :
    Tendsto (fun t : ℝ =>
      (‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k +
        ‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k -
        4 * ‖x‖ ^ k) / t ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (k ^ 2 * ‖x‖ ^ (k - 2))) := by
  have norm_rpow_imag_centered_difference_tendsto : Tendsto (fun t : ℝ => (‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k - 2 * ‖x‖ ^ k) / t ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 ((k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) * (2 * x.im) ^ 2 + (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2)) := by
    let y := -Complex.I * x
    have hnorm : ‖y‖ = ‖x‖ := by
      dsimp [y]
      rw [norm_mul]
      simp
    have hplus : ∀ t : ℝ, ‖x + (t : ℂ) * Complex.I‖ = ‖y + (t : ℂ)‖ := by
      intro t
      have hm : (-Complex.I) * (x + (t : ℂ) * Complex.I) = y + (t : ℂ) := by
        dsimp [y]
        rw [mul_add]
        congr 1
        calc
          (-Complex.I) * ((t : ℂ) * Complex.I) = -((t : ℂ) * (Complex.I * Complex.I)) := by
            rw [neg_mul]
            ring
          _ = (t : ℂ) := by simp
      calc
        ‖x + (t : ℂ) * Complex.I‖ =
            ‖(-Complex.I) * (x + (t : ℂ) * Complex.I)‖ := by simp
        _ = ‖y + (t : ℂ)‖ := by rw [hm]
    have hminus : ∀ t : ℝ, ‖x - (t : ℂ) * Complex.I‖ = ‖y - (t : ℂ)‖ := by
      intro t
      have hm : (-Complex.I) * (x - (t : ℂ) * Complex.I) = y - (t : ℂ) := by
        dsimp [y]
        rw [mul_sub]
        congr 1
        calc
          (-Complex.I) * ((t : ℂ) * Complex.I) = -((t : ℂ) * (Complex.I * Complex.I)) := by
            rw [neg_mul]
            ring
          _ = (t : ℂ) := by simp
      calc
        ‖x - (t : ℂ) * Complex.I‖ =
            ‖(-Complex.I) * (x - (t : ℂ) * Complex.I)‖ := by simp
        _ = ‖y - (t : ℂ)‖ := by rw [hm]
    simpa [(show y.re = x.im by dsimp [y]; simp [Complex.mul_re]), hnorm] using ((norm_rpow_real_centered_difference_tendsto k y (by dsimp [y]; exact mul_ne_zero (by simp) hx)).congr' (show (fun t : ℝ => (‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k - 2 * ‖x‖ ^ k) / t ^ 2) =ᶠ[𝓝[≠] (0 : ℝ)] fun t => (‖y + (t : ℂ)‖ ^ k + ‖y - (t : ℂ)‖ ^ k - 2 * ‖y‖ ^ k) / t ^ 2 by filter_upwards [] with t; rw [hplus, hminus, hnorm]).symm)
  have radial_rpow_laplacian_coefficient : ((k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) * (2 * x.re) ^ 2 + (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2) + ((k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) * (2 * x.im) ^ 2 + (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2) = k ^ 2 * ‖x‖ ^ (k - 2) := by
    let p := k / 2
    let r := ‖x‖ ^ 2
    have hcoord : (2 * x.re) ^ 2 + (2 * x.im) ^ 2 = 4 * r := by
      dsimp [r]
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have hpow : r ^ (p - 2) * r = r ^ (p - 1) := by
      calc
        r ^ (p - 2) * r = r ^ (p - 2) * r ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = r ^ ((p - 2) + 1) := (Real.rpow_add (by dsimp [r]; positivity) (p - 2) 1).symm
        _ = r ^ (p - 1) := by congr 1; ring
    have hnormpow : r ^ (p - 1) = ‖x‖ ^ (k - 2) := by
      dsimp [p, r]
      rw [show k / 2 - 1 = (k - 2) / 2 by ring]
      exact (norm_rpow_eq_norm_sq_rpow x (k - 2)).symm
    calc
      _ = p * (p - 1) * r ^ (p - 2) *
            ((2 * x.re) ^ 2 + (2 * x.im) ^ 2) + 4 * p * r ^ (p - 1) := by
              dsimp [p, r]
              ring
      _ = p * (p - 1) * r ^ (p - 2) * (4 * r) +
            4 * p * r ^ (p - 1) := by rw [hcoord]
      _ = 4 * p ^ 2 * r ^ (p - 1) := by rw [← hpow]; ring
      _ = k ^ 2 * ‖x‖ ^ (k - 2) := by
            rw [hnormpow]
            dsimp [p]
            ring
  let dRe := (k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) *
    (2 * x.re) ^ 2 + (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2
  let dIm := (k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) *
    (2 * x.im) ^ 2 + (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2
  have hsum : Tendsto
      (fun t : ℝ =>
        (‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k - 2 * ‖x‖ ^ k) / t ^ 2 +
        (‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k -
          2 * ‖x‖ ^ k) / t ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (dRe + dIm)) := by
    simpa [dRe, dIm] using (norm_rpow_real_centered_difference_tendsto k x hx).add (norm_rpow_imag_centered_difference_tendsto)
  rw [show dRe + dIm = k ^ 2 * ‖x‖ ^ (k - 2) by exact (radial_rpow_laplacian_coefficient)] at hsum
  exact hsum.congr' (show (fun t : ℝ => (‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k + ‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k - 4 * ‖x‖ ^ k) / t ^ 2) =ᶠ[𝓝[≠] (0 : ℝ)] fun t => (‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k - 2 * ‖x‖ ^ k) / t ^ 2 + (‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k - 2 * ‖x‖ ^ k) / t ^ 2 by filter_upwards [] with t; ring).symm

end DOZZ.Proofs
