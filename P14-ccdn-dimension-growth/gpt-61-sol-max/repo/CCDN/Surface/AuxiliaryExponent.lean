/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Statements
import CCDN.ForMathlib.Log

/-! The numerical component of the corrected surface estimate. The auxiliary
 degree contributes a further factor d to the intersection degree, giving d^18
 after taking fourth powers. -/

public section
namespace CCDN

/-- For `d ≥ 16`, the exponent `1 / √d` is at most `1 / 4`. -/
lemma surface_inverse_sqrt_le_quarter {d : ℕ} (hd : 16 ≤ d) :
    1 / Real.sqrt ↑d ≤ (1 / 4 : ℝ) := by
  have hs : 4 ≤ Real.sqrt ↑d :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast hd)
  exact one_div_le_one_div_of_le (by norm_num) hs


variable {δ : ℕ} (hδ : 2 ≤ δ) {B : ℝ} (hB : 1 ≤ B) (hδB : ↑δ ≤ Real.log B)

include hδ hB hδB in
private lemma small_degree_rpow_weight  :
    ↑δ ^ 3 * B ^ (1 / (δ : ℝ)) ≤
      (48 * Real.exp 1) * B ^ (1 / 2 : ℝ) := by
  have hδ2 : (2 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hpoly : ↑δ ^ 3 ≤ 48 * Real.exp (↑δ / 2) := by
    have hh := Real.pow_div_factorial_le_exp (↑δ / 2)
      (show 0 ≤ (δ : ℝ) / 2 by positivity) 3
    norm_num at hh
    nlinarith
  have hexp : ↑δ / 2 + Real.log B / δ ≤ 1 + Real.log B / 2 := by
    have hc := div_mul_cancel₀ (Real.log B) hδ0.ne'
    nlinarith
  calc
    _ ≤ (48 * Real.exp (↑δ / 2)) * B ^ (1 / (δ : ℝ)) :=
      mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = 48 * Real.exp (↑δ / 2 + Real.log B / δ) := by
      grind [Real.rpow_def_of_pos, Real.exp_add]
    _ ≤ 48 * Real.exp (1 + Real.log B / 2) := by
      simp_all
    _ = _ := by
      grind [Real.exp_add, Real.rpow_def_of_pos]

include hδ hB hδB in
/-- For curve degrees between two and log B, the degree factors can be
 absorbed uniformly into a square-root box bound. -/
private theorem curveBound_small_degree_uniform  :
    curveBound δ B ≤ (96 * Real.exp 1) * B ^ (1 / 2 : ℝ) * (Real.log B + 1) := by
  have hlog := Real.log_nonneg hB
  have hh := mul_le_mul (small_degree_rpow_weight hδ hB hδB)
    (show Real.log B + δ ≤ 2 * (Real.log B + 1) by linarith)
    (show 0 ≤ Real.log B + δ by positivity) (by positivity)
  unfold curveBound
  convert hh using 1
  ring


variable {ι : Type*}

/-- The sum of fourth powers of nonnegative component degrees is bounded
 by the fourth power of their total degree. -/
private lemma sum_fourth_powers_le_fourth_power_sum 
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∑ i ∈ s, (a i) ^ 4 ≤ (∑ i ∈ s, a i) ^ 4 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := s) (f := fun i => a i ^ 2)
    (fun i _ => sq_nonneg (a i))
  have h' := pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => sq_nonneg (a i)))
    (Finset.sum_sq_le_sq_sum_of_nonneg ha) 2
  simpa only [← pow_mul, Nat.reduceMul] using h.trans h'

/-- Above the logarithmic degree threshold, the curve bound is controlled
 by the fourth power of the curve degree. -/
private theorem curveBound_large_degree {δ : ℕ} (hδ : 0 < δ) {B : ℝ}
    (hB : 1 ≤ B) (hBδ : Real.log B ≤ ↑δ) :
    curveBound δ B ≤ (2 * Real.exp 1) * ↑δ ^ 4 := by
  have hδ0 : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hB0 : 0 < B := by linarith
  have hlog := Real.log_nonneg hB
  have hpow : B ^ (1 / (δ : ℝ)) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hB0]
    apply Real.exp_le_exp.mpr
    simpa only [mul_one_div] using (div_le_one hδ0).mpr hBδ
  have hh := mul_le_mul
    (mul_le_mul_of_nonneg_left hpow (show 0 ≤ ↑δ ^ 3 by positivity))
    (show Real.log B + δ ≤ 2 * δ by linarith)
    (show 0 ≤ Real.log B + δ by positivity)
    (show 0 ≤ ↑δ ^ 3 * Real.exp 1 by positivity)
  unfold curveBound
  convert hh using 1
  ring

/-- Both degree ranges can be summed using their common total-degree
 budget. Every component here has degree at least two. -/
private theorem sum_curveBound_le_degree_budget  (s : Finset ι) (δ : ι → ℕ)
    {B D : ℝ} (hB : 1 ≤ B) (hδ : ∀ i ∈ s, 2 ≤ δ i)
    (hD : (∑ i ∈ s, (δ i : ℝ)) ≤ D) :
    ∑ i ∈ s, curveBound (δ i) B ≤
      D * ((96 * Real.exp 1) * B ^ (1 / 2 : ℝ) * (Real.log B + 1)) +
        (2 * Real.exp 1) * D ^ 4 := by
  let U := (96 * Real.exp 1) * B ^ (1 / 2 : ℝ) * (Real.log B + 1)
  have hlog := Real.log_nonneg hB
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hS : 0 ≤ ∑ i ∈ s, (δ i : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
  have hpoint : ∀ i ∈ s, curveBound (δ i) B ≤
      (δ i : ℝ) * U + (2 * Real.exp 1) * (δ i : ℝ) ^ 4 := by
    intro i hi
    by_cases hsmall : (δ i : ℝ) ≤ Real.log B
    · have hc := curveBound_small_degree_uniform (hδ i hi) hB hsmall
      have hd1 : (1 : ℝ) ≤ δ i := by exact_mod_cast (show 1 ≤ δ i by have := hδ i hi; omega)
      have hu : U ≤ (δ i : ℝ) * U := by nlinarith
      have hp : 0 ≤ (2 * Real.exp 1) * (δ i : ℝ) ^ 4 := by positivity
      exact hc.trans (hu.trans (le_add_of_nonneg_right hp))
    · have hc := curveBound_large_degree (show 0 < δ i by have := hδ i hi; omega)
        hB (le_of_lt (lt_of_not_ge hsmall))
      exact hc.trans (le_add_of_nonneg_left (by positivity))
  calc
    _ ≤ ∑ i ∈ s, ((δ i : ℝ) * U + (2 * Real.exp 1) * (δ i : ℝ) ^ 4) :=
      Finset.sum_le_sum hpoint
    _ = (∑ i ∈ s, (δ i : ℝ)) * U +
        (2 * Real.exp 1) * ∑ i ∈ s, (δ i : ℝ) ^ 4 := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    _ ≤ D * U + (2 * Real.exp 1) * D ^ 4 := by
      apply add_le_add (mul_le_mul_of_nonneg_right hD hU)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (sum_fourth_powers_le_fourth_power_sum s (fun i => (δ i : ℝ))
        (fun _ _ => by positivity)).trans (pow_le_pow_left₀ hS hD 4)

/-- The whole numerical contribution of the nonlinear curve components in
 the surface argument, with the corrected d^18 factor. -/
theorem sum_curveBound_le_surface_degree_budget 
    (s : Finset ι) (δ : ι → ℕ) {d : ℕ} (hd : 16 ≤ d)
    {B C : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) (hδ : ∀ i ∈ s, 2 ≤ δ i)
    (hD : (∑ i ∈ s, (δ i : ℝ)) ≤
      C * ↑d ^ (9 / 2 : ℝ) * B ^ (1 / Real.sqrt d)) :
    ∑ i ∈ s, curveBound (δ i) B ≤
      Real.exp 1 * (480 * C + 2 * C ^ 4) * ↑d ^ 18 * B := by
  have hS : 0 ≤ ∑ i ∈ s, (δ i : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
  have hsplit := sum_curveBound_le_degree_budget s δ hB hδ (le_refl _)
  have hsmall := (show (∑ i ∈ s, ↑(δ i)) * ((96 : ℝ) * Real.exp (1 : ℝ) * B ^ (1 / 2 : ℝ) * (Real.log B + (1 : ℝ))) ≤
                     (480 : ℝ) * Real.exp (1 : ℝ) * C * ↑d ^ (18 : ℕ) * B from (by
                   have hlog := Real.log_nonneg hB
                   have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
                   have hdp := by
                     simpa only [Real.rpow_ofNat] using
                       Real.rpow_le_rpow_of_exponent_le hd1 (show (9 / 2 : ℝ) ≤ 18 by norm_num)
                   calc
                     _ ≤ (C * ↑d ^ (9 / 2 : ℝ) * B ^ (1 / Real.sqrt d)) *
                         ((96 * Real.exp 1) * B ^ (1 / 2 : ℝ) * (Real.log B + 1)) :=
                       mul_le_mul_of_nonneg_right hD (by positivity)
                     _ = (96 * Real.exp 1) * C * ↑d ^ (9 / 2 : ℝ) *
                         (B ^ (1 / Real.sqrt d) * (B ^ (1 / 2 : ℝ) * (Real.log B + 1))) := by ring
                     _ ≤ (96 * Real.exp 1) * C * ↑d ^ (9 / 2 : ℝ) * (5 * B) :=
                       mul_le_mul_of_nonneg_left ((show B ^ ((1 : ℝ) / √↑d) * (B ^ (1 / 2 : ℝ) * (Real.log B + (1 : ℝ))) ≤ (5 : ℝ) * B from (by
                                                    have hB0 : 0 < B := by linarith
                                                    have hlog := by
                                                      have hh := Real.rpow_half_mul_log_add_le (ε := (1 / 4 : ℝ)) (D := 1)
                                                        hB (by norm_num) (by norm_num)
                                                      norm_num at hh ⊢
                                                      exact hh
                                                    have hexp : 1 / Real.sqrt ↑d + (3 / 4 : ℝ) ≤ 1 := by
                                                      grind [surface_inverse_sqrt_le_quarter]
                                                    calc
                                                      _ ≤ B ^ (1 / Real.sqrt ↑d) * (5 * B ^ (3 / 4 : ℝ)) :=
                                                        mul_le_mul_of_nonneg_left hlog (by positivity)
                                                      _ = 5 * B ^ (1 / Real.sqrt ↑d + (3 / 4 : ℝ)) := by
                                                        rw [Real.rpow_add hB0]
                                                        ring
                                                      _ ≤ 5 * B := by
                                                        simpa only [Real.rpow_one] using
                                                          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hB hexp)
                                                            (show 0 ≤ 5 by norm_num)))) (by positivity)
                     _ = (480 * Real.exp 1) * C * ↑d ^ (9 / 2 : ℝ) * B := by ring
                     _ ≤ _ := by gcongr))
  have hlarge := mul_le_mul_of_nonneg_left
    ((show (∑ i ∈ s, ↑(δ i)) ^ (4 : ℕ) ≤ C ^ (4 : ℕ) * ↑d ^ (18 : ℕ) * B from (by
       have hd0 : (0 : ℝ) < d := by positivity
       have hB0 : 0 < B := by linarith
       have hpow := pow_le_pow_left₀ hS hD 4
       rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hd0.le (9 / 2 : ℝ) 4,
         ← Real.rpow_mul_natCast hB0.le (1 / Real.sqrt d) 4] at hpow
       norm_num only [show (9 / 2 : ℝ) * 4 = 18 by norm_num, Real.rpow_ofNat] at hpow
       have hexp : (1 / Real.sqrt ↑d) * 4 ≤ 1 := by
         grind [surface_inverse_sqrt_le_quarter]
       have hbox := by
         simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB hexp
       exact hpow.trans (mul_le_mul_of_nonneg_left hbox (by positivity)))))
    (show 0 ≤ 2 * Real.exp 1 by positivity)
  calc
    _ ≤ _ := hsplit
    _ ≤ (480 * Real.exp 1) * C * ↑d ^ 18 * B +
        (2 * Real.exp 1) * (C ^ 4 * ↑d ^ 18 * B) := add_le_add hsmall hlarge
    _ = _ := by ring

end CCDN
