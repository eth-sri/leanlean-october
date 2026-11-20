/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Explicit exponent margins for the small-degree surface argument.
The estimates hold uniformly for every degree at least five and absorb any
fixed power of the logarithm; geometric covering hypotheses are separate. -/

@[expose] public section
namespace CCDN
noncomputable section

variable {d : ℕ} (hd : 5 ≤ d) (k : ℕ)

include hd in
/-- For every natural number `d ≥ 5`, `1 / √d ≤ 9 / 20`. -/
theorem surface_inverse_sqrt_le_nine_twentieths :
    1 / Real.sqrt (d : ℝ) ≤ (9 / 20 : ℝ) := by
  have hdR : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : (20 / 9 : ℝ) ≤ Real.sqrt (d : ℝ) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  linarith [one_div_le_one_div_of_le (by norm_num) hs]

/-- A fixed logarithmic power costs at most any prescribed positive power,
with an explicit constant independent of the box radius. -/
theorem logarithm_add_one_pow_le_rpow {ε B : ℝ}
    (hε : 0 < ε) (hB : 1 ≤ B) :
    (Real.log B + 1) ^ k ≤
      ((k.factorial : ℝ) / ε ^ k * Real.exp ε) * B ^ ε := by
  have hB0 : 0 < B := by linarith
  have hlog := Real.log_nonneg hB
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hh := Real.pow_div_factorial_le_exp (ε * (Real.log B + 1))
    (by positivity) k
  have he : Real.exp (ε * (Real.log B + 1)) = Real.exp ε * B ^ ε := by
    rw [Real.rpow_def_of_pos hB0, ← Real.exp_add]
    ring
  rw [he, mul_pow] at hh
  have hm := (div_le_iff₀ hfac).mp hh
  calc
    _ ≤ (Real.exp ε * B ^ ε * k.factorial) / ε ^ k := by
      apply (le_div_iff₀ (pow_pos hε k)).mpr
      grind
    _ = _ := by ring

include hd in
/-- Retained nonlinear curves with square-root box count and any fixed
polylogarithmic loss contribute O(B) once their number has the
B^(1/sqrt(d)) scale, for every d>=5. -/
theorem surface_nonlinear_polylog_weight
    {B : ℝ} (hB : 1 ≤ B) :
    B ^ (1 / Real.sqrt (d : ℝ) + 1 / 2) * (Real.log B + 1) ^ k ≤
      ((k.factorial : ℝ) / (1 / 20 : ℝ) ^ k * Real.exp (1 / 20)) * B := by
  let C := k.factorial / (1 / 20) ^ k * Real.exp (1 / 20)
  have hC : 0 ≤ C := by positivity
  have he : 1 / Real.sqrt (d : ℝ) + 1 / 2 + 1 / 20 ≤ (1 : ℝ) := by
    grind [surface_inverse_sqrt_le_nine_twentieths]
  calc
    _ ≤ B ^ (1 / Real.sqrt d + 1 / 2) * (C * B ^ (1 / 20)) :=
      mul_le_mul_of_nonneg_left (logarithm_add_one_pow_le_rpow k (by simp) hB) (by positivity)
    _ = C * B ^ (1 / Real.sqrt d + 1 / 2 + 1 / 20) := by
      grind [Real.rpow_add, Real.sqrt]
    _ ≤ C * B := by
      exact mul_le_mul_of_nonneg_left
        (by simpa using Real.rpow_le_rpow_of_exponent_le hB he) hC

open Real

def logWeight := Nat.factorial 4 / (1/20:ℝ)^4 * exp (1/20)

include hd in
lemma retained_curve_cost {A D B : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hB : 1 ≤ B) :
    A*B^(1/sqrt (d:ℝ))*(log B+1)*(B^(1/2:ℝ)*(log B+1)^3+(D*(log B+1))^3) ≤
    A*(1+D^3)*logWeight*B := by
  let T := log B+1
  have hT : 0 ≤ T := by dsimp [T]; linarith [log_nonneg hB]
  have hs := one_le_rpow hB (by norm_num : (0:ℝ)≤1/2)
  have hw := surface_nonlinear_polylog_weight hd 4 hB
  rw [rpow_add (by linarith)] at hw
  change _*_*T*(_*T^3+(D*T)^3) ≤ _
  calc
    _ ≤ A*B^(1/sqrt (d:ℝ))*T*(B^(1/2:ℝ)*T^3+B^(1/2:ℝ)*(D*T)^3) := by gcongr; exact le_mul_of_one_le_left (by positivity) hs
    _ = (A*(1+D^3))*(B^(1/sqrt (d:ℝ))*B^(1/2:ℝ)*T^4) := by ring
    _ ≤ (A*(1+D^3))*(logWeight*B) := mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by ring

end
end CCDN
