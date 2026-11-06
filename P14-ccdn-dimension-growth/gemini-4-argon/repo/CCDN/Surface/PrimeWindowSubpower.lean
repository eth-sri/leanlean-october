/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Surface.CongruencePrimeWindow
import CCDN.Analysis.SmallDegreeSurfaceNumerics

/-! The number of subsets and edges of a common logarithmic prime window
costs only an arbitrarily small positive power of the box radius. Constants
are fixed before the radius, including the bounded range near B = 1. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset

/-- For `K, R ≥ 1` and `k : ℕ`, there is a constant `C` such that, for every degree `d ≥ 5` and
every `B ≥ 1`, the prime window `W` of logarithmic size `K (log B + 1)` satisfies
`#W R^#W B^(2/√d) (log B + 1)^k ≤ C B`. -/
theorem congruencePrimeWindow_surface_residual_bound {K R : ℝ}
    (hK : 1 ≤ K) (hR : 1 ≤ R) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 5 ≤ d → ∀ B : ℝ, 1 ≤ B →
      ((congruencePrimeWindow (K * (Real.log B + 1))).card *
        R ^ (congruencePrimeWindow (K * (Real.log B + 1))).card) *
        B ^ (2 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ^ k ≤ C * B := by
  let R' := 2 * R
  have hR' : 1 ≤ R' := by dsimp [R']; linarith
  have hR'0 : 0 < R' := zero_lt_one.trans_le hR'
  have hlogR' : 0 ≤ Real.log R' := Real.log_nonneg hR'
  let A := (Real.log 4 + 4) * scalingPrimeRatio
  have hA : 0 < A := by
    have := scalingPrimeRatio_one_le
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [A]; positivity
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D := A * K * Real.log R' / (1 / 40 : ℝ) + 1
  let E := A * Real.exp D / Real.log 2 * Real.log R'
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  let C₁ := Real.exp (E + 1 / 40)
  have hC₁ : 0 < C₁ := Real.exp_pos _
  let C₂ := (k.factorial : ℝ) / (1 / 40 : ℝ) ^ k * Real.exp (1 / 40)
  have hC₂ : 0 < C₂ := by dsimp only [C₂]; positivity
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, fun d hd B hB => ?_⟩
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  let L := K * (Real.log B + 1)
  let m := (congruencePrimeWindow L).card
  have hL : 1 ≤ L := by dsimp only [L]; nlinarith
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hcard : (m : ℝ) * Real.log L ≤ A * L := congruencePrimeWindow_card_log_bound hL
  have hcard2 : (m : ℝ) * Real.log 2 ≤ A * L := by
    rw [show (m : ℝ) * Real.log 2 = ∑ _p ∈ congruencePrimeWindow L, Real.log 2 by simp [m]]
    exact (sum_le_sum fun p hp => Real.log_le_log (by norm_num)
      (mod_cast ((mem_congruencePrimeWindow hL).mp hp).1.two_le)).trans
      (congruencePrimeWindow_log_upper hL)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hbound : (m : ℝ) * Real.log R' ≤ E + (1 / 40 : ℝ) * (Real.log B + 1) := by
    by_cases hlarge : D ≤ Real.log L
    · have hd' : A * K * Real.log R' ≤ (1 / 40 : ℝ) * Real.log L := by
        nlinarith [(div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 40)).mp
          (show A * K * Real.log R' / (1 / 40 : ℝ) ≤ Real.log L by dsimp only [D] at hlarge; linarith)]
      have hmul := mul_le_mul_of_nonneg_left hd' hm0
      have hupper := mul_le_mul_of_nonneg_left hcard (by norm_num : (0 : ℝ) ≤ 1 / 40)
      have hmain : (m : ℝ) * Real.log R' ≤ (1 / 40 : ℝ) * (Real.log B + 1) :=
        (mul_le_mul_iff_left₀ (mul_pos hA hK0)).mp (by dsimp only [L] at hupper; nlinarith)
      nlinarith
    · have hLbound : L ≤ Real.exp D := by
        simpa only [Real.exp_log hL0] using Real.exp_le_exp.mpr (le_of_not_ge hlarge)
      have hm' : (m : ℝ) ≤ A * Real.exp D / Real.log 2 :=
        (le_div_iff₀ hlog2).mpr (hcard2.trans (mul_le_mul_of_nonneg_left hLbound hA.le))
      have hh : (m : ℝ) * Real.log R' ≤ E := mul_le_mul_of_nonneg_right hm' hlogR'
      nlinarith
  have hexp := Real.exp_le_exp.mpr hbound
  rw [← Real.log_pow, Real.exp_log (pow_pos hR'0 _)] at hexp
  have hpow : R' ^ m ≤ C₁ * B ^ (1 / 40 : ℝ) :=
    hexp.trans_eq (by dsimp [C₁]; rw [Real.rpow_def_of_pos hB0, ← Real.exp_add]; congr 1; ring)
  have hm : (m : ℝ) ≤ 2 ^ m := mod_cast (Nat.le_of_lt m.lt_two_pow_self)
  have h₁ : (m : ℝ) * R ^ m ≤ C₁ * B ^ (1 / 40 : ℝ) :=
    ((mul_le_mul_of_nonneg_right hm (by positivity)).trans_eq (mul_pow _ _ _).symm).trans hpow
  have h₂ : (Real.log B + 1) ^ k ≤ C₂ * B ^ (1 / 40 : ℝ) :=
    logarithm_add_one_pow_le_rpow k (by norm_num : (0 : ℝ) < 1 / 40) hB
  have hα : 2 / Real.sqrt (d : ℝ) ≤ 19 / 20 := by
    have hh := surface_inverse_sqrt_le_nine_twentieths hd
    rw [show 2 / Real.sqrt (d : ℝ) = 2 * (1 / Real.sqrt (d : ℝ)) by ring]
    linarith
  calc
    _ ≤ (C₁ * B ^ (1 / 40 : ℝ)) * B ^ (2 / Real.sqrt (d : ℝ)) * (C₂ * B ^ (1 / 40 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right h₁ (Real.rpow_nonneg hB0.le _)) h₂
        (by positivity) (by positivity)
    _ = (C₁ * C₂) * B ^ (2 / Real.sqrt (d : ℝ) + 1 / 20) := by
      rw [Real.rpow_add hB0, show B ^ (1 / 20 : ℝ) = B ^ (1 / 40 : ℝ) * B ^ (1 / 40 : ℝ) by
        rw [← Real.rpow_add hB0]; norm_num]
      ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hB (by linarith : 2 / Real.sqrt (d : ℝ) + 1 / 20 ≤ 1))
      (mul_pos hC₁ hC₂).le).trans_eq (by rw [Real.rpow_one])

end
end CCDN
