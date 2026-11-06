/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Analysis.SmallDegreeSurfaceNumerics
import CCDN.ClassGroup.PrimeFactorSubpower

/-! Uniform numerical absorption for quadratic class-group descent.
The prime-factor and logarithmic losses fit in the positive exponent
margin between the base-field and extension-field estimates. -/

namespace CCDN

theorem primeFactors_polylog_subpower (a k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 1 ≤ D →
      (2 : ℝ) ^ (a * D.primeFactors.card) * (Real.log (D : ℝ) + 1) ^ k ≤
        C * (D : ℝ) ^ ε := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨A, hA, hprime⟩ := two_pow_primeFactors_subpower a hhalf
  let L : ℝ := k.factorial / (ε / 2) ^ k * Real.exp (ε / 2)
  have hL : 0 < L := by positivity
  refine ⟨A * L, mul_pos hA hL, ?_⟩
  intro D hD
  have hDR : (1 : ℝ) ≤ D := mod_cast hD
  have hDpos : (0 : ℝ) < D := by linarith
  have hlog := logarithm_add_one_pow_le_rpow k hhalf hDR
  calc
    _ ≤ (A * D ^ (ε / 2)) * (L * D ^ (ε / 2)) :=
      mul_le_mul (hprime D hD) hlog (by positivity) (by positivity)
    _ = (A * L) * D ^ ε := by
      have hpow : D ^ ε =
          (D : ℝ) ^ (ε / 2) * (D : ℝ) ^ (ε / 2) := by
        rw [← Real.rpow_add hDpos]
        congr 1
        ring
      grind

/-- Exact numerical quadratic descent. The constant is chosen before
the discriminant, base discriminant, and class-group cardinalities.
There is no logarithmic loss in the conclusion. -/
theorem quadratic_class_group_numeric_descent (m : ℕ) (hm : 2 ≤ m)
    (C : ℝ) (hC : 0 < C) :
    ∃ A : ℝ, 0 < A ∧ ∀ D : ℕ, 1 ≤ D → ∀ x h H : ℝ,
      1 ≤ x → x ^ 2 ≤ (D : ℝ) → 0 ≤ h →
      h ≤ C * x ^ (1 / 2 - 1 / (2 * (m : ℝ))) * (Real.log x + 1) →
      H ≤ (h * (2 : ℝ) ^ ((2 * m) * D.primeFactors.card + m)) ^ 2 →
      H ≤ A * (D : ℝ) ^ (1 / 2 - 1 / (2 * ((2 * m : ℕ) : ℝ))) := by
  have hmR : (2 : ℝ) ≤ m := mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  let ε : ℝ := 1 / (4 * m)
  have hε : 0 < ε := by positivity
  obtain ⟨A, hA, hweight⟩ := primeFactors_polylog_subpower (4 * m) 2 hε
  refine ⟨C ^ 2 * (2 : ℝ) ^ (2 * m) * A, by positivity, ?_⟩
  intro D hD x h H hx hxD hh hbound hH
  have hDR : (1 : ℝ) ≤ D := mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hx0 : 0 < x := by linarith
  have hxD' : x ≤ D := by nlinarith
  have hlogx := Real.log_nonneg hx
  have hlogD := Real.log_le_log hx0 hxD'
  let α : ℝ := 1 / 2 - 1 / (2 * m)
  have hα : 0 ≤ α := by bound
  have hgeom : (x ^ α) ^ 2 ≤ D ^ α := by
    rw [Real.rpow_pow_comm hx0.le]
    bound
  have hlogs : (Real.log x + 1) ^ 2 ≤ (Real.log D + 1) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  let P : ℝ := (2 : ℝ) ^ ((2 * m) * D.primeFactors.card + m)
  have hP : P ^ 2 = (2 : ℝ) ^ (2 * m) * (2 : ℝ) ^ ((4 * m) * D.primeFactors.card) := by ring
  have hmain :=
    mul_le_mul (mul_le_mul_of_nonneg_left hgeom (sq_nonneg C)) hlogs
      (sq_nonneg _) (by positivity)
  have hexponent : α + ε = 1 / 2 - 1 / (2 * ((2 * m : ℕ) : ℝ)) := by grind
  calc
    H ≤ (h * P) ^ 2 := hH
    _ ≤ ((C * x ^ α * (Real.log x + 1)) * P) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hh (by positivity))
        (mul_le_mul_of_nonneg_right hbound (by positivity)) 2
    _ = (C ^ 2 * (x ^ α) ^ 2 * (Real.log x + 1) ^ 2) * P ^ 2 := by ring
    _ ≤ (C ^ 2 * D ^ α * (Real.log D + 1) ^ 2) * P ^ 2 :=
      mul_le_mul_of_nonneg_right hmain (sq_nonneg P)
    _ = (C ^ 2 * (2 : ℝ) ^ (2 * m)) * D ^ α *
        ((2 : ℝ) ^ ((4 * m) * D.primeFactors.card) * (Real.log (D : ℝ) + 1) ^ 2) := by
      rw [hP]
      ring
    _ ≤ (C ^ 2 * (2 : ℝ) ^ (2 * m)) * D ^ α * (A * D ^ ε) :=
      mul_le_mul_of_nonneg_left (hweight D hD) (by positivity)
    _ = (C ^ 2 * (2 : ℝ) ^ (2 * m) * A) *
        (D : ℝ) ^ (1 / 2 - 1 / (2 * ((2 * m : ℕ) : ℝ))) := by
      rw [← hexponent, Real.rpow_add hD0]
      ring

