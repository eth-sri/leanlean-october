/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Statements
import CCDN.ForMathlib.Log

/-! The numerical component of the corrected surface estimate. The auxiliary
 degree contributes a further factor d to the intersection degree, giving d^18
 after taking fourth powers. -/

@[expose] public section
namespace CCDN
noncomputable section

private lemma surface_inverse_sqrt_le_quarter {d : ℕ} (hd : 16 ≤ d) :
    1 / Real.sqrt (d : ℝ) ≤ (1 / 4 : ℝ) :=
  one_div_le_one_div_of_le (by norm_num) (Real.le_sqrt_of_sq_le (by exact_mod_cast hd))

/-- A single majorant for a component of degree at least two, with the logarithm
absorbed into a quarter power in the small-degree range. -/
private lemma curveBound_component_le {δ : ℕ} (hδ : 2 ≤ δ) {B : ℝ} (hB : 1 ≤ B) :
    curveBound δ B ≤ 480 * Real.exp 1 * (δ : ℝ) * B ^ (3 / 4 : ℝ) +
      2 * Real.exp 1 * (δ : ℝ) ^ 4 := by
  have hδ2 : (2 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hδ0 : (0 : ℝ) < δ := by positivity
  have hb : 0 < B := by linarith
  have hl := Real.log_nonneg hB
  unfold curveBound
  by_cases h : (δ : ℝ) ≤ Real.log B
  · have hpoly : (δ : ℝ) ^ 3 ≤ 48 * Real.exp ((δ : ℝ) / 2) := by
      linarith [Real.pow_div_factorial_le_exp ((δ : ℝ) / 2) (by positivity) 3]
    have hexp : (δ : ℝ) / 2 + Real.log B / δ ≤ 1 + Real.log B / 2 := by
      apply le_of_mul_le_mul_right _ hδ0
      rw [add_mul, div_mul_cancel₀ _ hδ0.ne']
      nlinarith only [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hδ2)]
    have hw : (δ : ℝ) ^ 3 * B ^ (1 / (δ : ℝ)) ≤ 48 * Real.exp 1 * B ^ (1 / 2 : ℝ) := by
      calc
        _ ≤ 48 * Real.exp ((δ : ℝ) / 2) * B ^ (1 / (δ : ℝ)) := by gcongr
        _ = 48 * Real.exp ((δ : ℝ) / 2 + Real.log B / δ) := by
          rw [Real.rpow_def_of_pos hb, Real.exp_add, mul_one_div, mul_assoc]
        _ ≤ 48 * Real.exp (1 + Real.log B / 2) := by gcongr
        _ = _ := by rw [Real.exp_add, Real.rpow_def_of_pos hb, mul_one_div, mul_assoc]
    have hlog : B ^ (1 / 2 : ℝ) * (Real.log B + 1) ≤ 5 * B ^ (3 / 4 : ℝ) := by
      convert Real.rpow_half_mul_log_add_le (ε := 1 / 4) (D := 1) hB (by norm_num) (by norm_num) using 2 <;> norm_num
    calc
      _ ≤ (48 * Real.exp 1 * B ^ (1 / 2 : ℝ)) * (2 * (Real.log B + 1)) := by
        gcongr; linarith
      _ ≤ _ := by
        nlinarith only [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 96 * Real.exp 1 by positivity),
          mul_nonneg (show 0 ≤ 480 * Real.exp 1 * B ^ (3 / 4 : ℝ) by positivity)
            (show 0 ≤ (δ : ℝ) - 1 by linarith),
          show 0 ≤ 2 * Real.exp 1 * (δ : ℝ) ^ 4 by positivity]
  · have hp : B ^ (1 / (δ : ℝ)) ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos hb, mul_one_div, Real.exp_le_exp]
      exact (div_le_one hδ0).mpr (le_of_not_ge h)
    calc
      _ ≤ (δ : ℝ) ^ 3 * Real.exp 1 * (2 * δ) := by gcongr; linarith
      _ ≤ _ := by nlinarith only [show 0 ≤ 480 * Real.exp 1 * (δ : ℝ) * B ^ (3 / 4 : ℝ) by positivity]

private lemma sum_fourth_powers_le_fourth_power_sum {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∑ i ∈ s, (a i) ^ 4 ≤ (∑ i ∈ s, a i) ^ 4 := by
  calc
    _ ≤ ∑ i ∈ s, a i * (∑ j ∈ s, a j) ^ 3 := by
      refine Finset.sum_le_sum fun i hi => ?_
      have := ha i hi
      rw [pow_succ']
      gcongr
      exact Finset.single_le_sum ha hi
    _ = _ := by rw [← Finset.sum_mul, ← pow_succ']

/-- Total nonlinear contribution with the corrected eighteenth power of the surface degree. -/
theorem sum_curveBound_le_surface_degree_budget {ι : Type*} (s : Finset ι) (δ : ι → ℕ)
    {d : ℕ} (hd : 16 ≤ d) {B C : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) (hδ : ∀ i ∈ s, 2 ≤ δ i)
    (hD : (∑ i ∈ s, (δ i : ℝ)) ≤ C * (d : ℝ) ^ (9 / 2 : ℝ) * B ^ (1 / Real.sqrt d)) :
    ∑ i ∈ s, curveBound (δ i) B ≤
      Real.exp 1 * (480 * C + 2 * C ^ 4) * (d : ℝ) ^ 18 * B := by
  let S := ∑ i ∈ s, (δ i : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hB0 : 0 < B := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hroot := surface_inverse_sqrt_le_quarter hd
  have hD' : S ≤ C * (d : ℝ) ^ (9 / 2 : ℝ) * B ^ (1 / 4 : ℝ) :=
    hD.trans (by gcongr)
  have hsmall : S * B ^ (3 / 4 : ℝ) ≤ C * (d : ℝ) ^ 18 * B := by
    refine (mul_le_mul_of_nonneg_right hD' (by positivity)).trans ?_
    rw [mul_assoc, ← Real.rpow_add hB0, show (1 / 4 + 3 / 4 : ℝ) = 1 by norm_num, Real.rpow_one]
    gcongr
    exact (Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num : (9 / 2 : ℝ) ≤ 18)).trans_eq
      (Real.rpow_natCast _ 18)
  have hlarge : S ^ 4 ≤ C ^ 4 * (d : ℝ) ^ 18 * B := by
    refine (pow_le_pow_left₀ hS hD' 4).trans_eq ?_
    rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast (by positivity), ← Real.rpow_mul_natCast hB0.le]
    norm_num
  calc
    _ ≤ ∑ i ∈ s, (480 * Real.exp 1 * (δ i : ℝ) * B ^ (3 / 4 : ℝ) +
        2 * Real.exp 1 * (δ i : ℝ) ^ 4) := Finset.sum_le_sum fun i hi => curveBound_component_le (hδ i hi) hB
    _ = 480 * Real.exp 1 * (S * B ^ (3 / 4 : ℝ)) + 2 * Real.exp 1 * ∑ i ∈ s, (δ i : ℝ) ^ 4 := by
      simp [S, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ ≤ _ := by
      have hfour := (sum_fourth_powers_le_fourth_power_sum s (fun i => (δ i : ℝ))
        (fun _ _ => by positivity)).trans hlarge
      linarith only [mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 480 * Real.exp 1 by positivity),
        mul_le_mul_of_nonneg_left hfour (show 0 ≤ 2 * Real.exp 1 by positivity)]

end
end CCDN
