/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Surface.CongruencePrimeWindow
import CCDN.Analysis.SmallDegreeSurfaceNumerics

/-! The number of subsets and edges of a common logarithmic prime window
costs only an arbitrarily small positive power of the box radius. Constants
are fixed before the radius, including the bounded range near B = 1. -/

namespace CCDN
open Finset

section
variable {K R ε : ℝ} (hK : 1 ≤ K) (hR : 1 ≤ R) (hε : 0 < ε)
include hK hR hε

/-- A uniform bound for any fixed exponential in the size of the window.
This retains the arbitrary epsilon needed to absorb residue multiplicities. -/
theorem congruencePrimeWindow_pow_subpower
    :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 1 ≤ B →
      R ^ (congruencePrimeWindow (K * (Real.log B + 1))).card ≤ C * B ^ ε := by
  let A := (Real.log 4 + 4) * scalingPrimeRatio
  have hA : 0 < A := by
    have ha := scalingPrimeRatio_one_le
    positivity
  have hK0 := zero_lt_one.trans_le hK
  have hR0 := zero_lt_one.trans_le hR
  have hlogR := Real.log_nonneg hR
  let D := A * K * Real.log R / ε + 1
  let E := A * Real.exp D / Real.log 2 * Real.log R
  have hE : 0 ≤ E := by positivity
  refine ⟨Real.exp (E + ε), Real.exp_pos _, ?_⟩
  intro B hB
  have hB0 := zero_lt_one.trans_le hB
  have hlogB := Real.log_nonneg hB
  let L := K * (Real.log B + 1)
  let m := (congruencePrimeWindow L).card
  have hL : 1 ≤ L := by nlinarith
  have hL0 := zero_lt_one.trans_le hL
  have hcard :=
    congruencePrimeWindow_card_log_bound hL
  have hcard2 : (congruencePrimeWindow L).card * Real.log 2 ≤
      (Real.log 4 + 4) * scalingPrimeRatio * L := by
    calc
      _ = ∑ _p ∈ congruencePrimeWindow L, Real.log 2 := by simp
      _ ≤ ∑ p ∈ congruencePrimeWindow L, Real.log p := by
        apply sum_le_sum
        intro p hp
        exact Real.log_le_log (by norm_num)
          (mod_cast ((mem_congruencePrimeWindow hL).mp hp).1.two_le)
      _ ≤ _ := congruencePrimeWindow_log_upper hL
  have hbound : m * Real.log R ≤ E + ε * (Real.log B + 1) := by
    by_cases hlarge : D ≤ Real.log L
    · have hd : A * K * Real.log R / ε ≤ Real.log L := by grind
      have hd' : A * K * Real.log R ≤ ε * Real.log L := by
        have hh := (div_le_iff₀ hε).mp hd
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hd' (Nat.cast_nonneg m)
      have hupper := mul_le_mul_of_nonneg_left hcard hε.le
      have hmain : m * Real.log R ≤ ε * (Real.log B + 1) := by
        apply (mul_le_mul_iff_left₀ (mul_pos hA hK0)).mp
        grind
      nlinarith
    · have hLbound : L ≤ Real.exp D := by
        have hh := Real.exp_le_exp.mpr (le_of_not_ge hlarge)
        rwa [Real.exp_log hL0] at hh
      have hm' : m ≤ A * Real.exp D / Real.log 2 := by
        apply (le_div_iff₀ (Real.log_pos (by norm_num))).mpr
        nlinarith
      have hh := mul_le_mul_of_nonneg_right hm' hlogR
      nlinarith
  have hexp := Real.exp_le_exp.mpr hbound
  rw [← Real.log_pow, Real.exp_log (pow_pos hR0 _)] at hexp
  have heq : Real.exp (E + ε * (Real.log B + 1)) =
      Real.exp (E + ε) * B ^ ε := by
    rw [Real.rpow_def_of_pos hB0, ← Real.exp_add]
    congr 1
    ring
  rwa [heq] at hexp

/-- The edge count of the subset lattice, together with a fixed cost per
selected prime, also has arbitrarily small power growth. -/
theorem congruencePrimeWindow_edge_subpower
    :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 1 ≤ B →
      (congruencePrimeWindow (K * (Real.log B + 1))).card *
        R ^ (congruencePrimeWindow (K * (Real.log B + 1))).card ≤ C * B ^ ε := by
  obtain ⟨C, hC, hpow⟩ := congruencePrimeWindow_pow_subpower hK
    (show 1 ≤ 2 * R by linarith) hε
  refine ⟨C, hC, ?_⟩
  intro B hB
  let m := (congruencePrimeWindow (K * (Real.log B + 1))).card
  have hm : (m : ℝ) ≤ 2 ^ m := mod_cast (Nat.le_of_lt m.lt_two_pow_self)
  calc
    _ ≤ (2 : ℝ) ^ m * R ^ m := mul_le_mul_of_nonneg_right hm (by positivity)
    _ = (2 * R) ^ m := (mul_pow _ _ _).symm
    _ ≤ _ := hpow B hB

end

variable {K R : ℝ} (hK : 1 ≤ K) (hR : 1 ≤ R) (k : ℕ)
include hK hR

/-- Both prime-subset multiplicities and any fixed logarithmic power fit
inside the exponent gap used by the surface argument. -/
theorem congruencePrimeWindow_edge_polylog_linear
    :
    ∃ C : ℝ, 0 < C ∧ ∀ α B : ℝ, α ≤ 19 / 20 → 1 ≤ B →
      ((congruencePrimeWindow (K * (Real.log B + 1))).card *
        R ^ (congruencePrimeWindow (K * (Real.log B + 1))).card) *
        B ^ α * (Real.log B + 1) ^ k ≤ C * B := by
  obtain ⟨C₁, hC₁, h₁⟩ := congruencePrimeWindow_edge_subpower hK hR
    (by norm_num : (0 : ℝ) < 1 / 40)
  let C₂ := k.factorial / (1 / 40 : ℝ) ^ k * Real.exp (1 / 40)
  have hC₂ : 0 < C₂ := by positivity
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro α B hα hB
  have hB0 := zero_lt_one.trans_le hB
  have hlogB := Real.log_nonneg hB
  have h₂ := logarithm_add_one_pow_le_rpow k (by norm_num : (0 : ℝ) < 1 / 40) hB
  calc
    _ ≤ (C₁ * B ^ (1 / 40 : ℝ)) * B ^ α * (C₂ * B ^ (1 / 40 : ℝ)) := by
      apply mul_le_mul
        (mul_le_mul_of_nonneg_right (h₁ B hB) (Real.rpow_nonneg hB0.le _)) h₂
      · positivity
      · positivity
    _ = (C₁ * C₂) * B ^ (α + 1 / 20) := by
      rw [Real.rpow_add hB0]
      have hh : B ^ (1 / 20 : ℝ) = B ^ (1 / 40 : ℝ) * B ^ (1 / 40 : ℝ) := by
        rw [← Real.rpow_add hB0]
        norm_num
      grind
    _ ≤ (C₁ * C₂) * B ^ (1 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hB (by linarith))
        (mul_pos hC₁ hC₂).le
    _ = _ := by simp_all

/-- For `K, R ≥ 1` and `k : ℕ`, there is a constant `C` such that, for every degree `d ≥ 5` and
every `B ≥ 1`, the prime window `W` of logarithmic size `K (log B + 1)` satisfies
`#W R^#W B^(2/√d) (log B + 1)^k ≤ C B`. -/
theorem congruencePrimeWindow_surface_residual_bound
    :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 5 ≤ d → ∀ B : ℝ, 1 ≤ B →
      ((congruencePrimeWindow (K * (Real.log B + 1))).card *
        R ^ (congruencePrimeWindow (K * (Real.log B + 1))).card) *
        B ^ (2 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ^ k ≤ C * B := by
  obtain ⟨C, hC, hbound⟩ := congruencePrimeWindow_edge_polylog_linear hK hR k
  refine ⟨C, hC, fun d hd B hB => hbound _ B ?_ hB⟩
  have hh := surface_inverse_sqrt_le_nine_twentieths hd
  have he : 2 / Real.sqrt d = 2 * (1 / Real.sqrt d) := by ring
  rw [he]
  linarith

