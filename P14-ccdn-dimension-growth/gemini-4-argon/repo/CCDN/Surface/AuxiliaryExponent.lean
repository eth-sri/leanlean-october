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

/-- For `d ≥ 16`, the exponent `1 / √d` is at most `1 / 4`. -/
lemma surface_inverse_sqrt_le_quarter {d : ℕ} (hd : 16 ≤ d) :
    1 / Real.sqrt (d : ℝ) ≤ (1 / 4 : ℝ) :=
  one_div_le_one_div_of_le (by norm_num) (Real.le_sqrt_of_sq_le (mod_cast hd))

/-- The whole numerical contribution of the nonlinear curve components in
 the surface argument, with the corrected d^18 factor. -/
theorem sum_curveBound_le_surface_degree_budget {ι : Type*}
    (s : Finset ι) (δ : ι → ℕ) {d : ℕ} (hd : 16 ≤ d)
    {B C : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) (hδ : ∀ i ∈ s, 2 ≤ δ i)
    (hD : (∑ i ∈ s, (δ i : ℝ)) ≤
      C * (d : ℝ) ^ (9 / 2 : ℝ) * B ^ (1 / Real.sqrt d)) :
    ∑ i ∈ s, curveBound (δ i) B ≤
      Real.exp 1 * (480 * C + 2 * C ^ 4) * (d : ℝ) ^ 18 * B := by
  let D := ∑ i ∈ s, (δ i : ℝ)
  let U := (96 * Real.exp 1) * B ^ (1 / 2 : ℝ) * (Real.log B + 1)
  have hB0 : 0 < B := by linarith
  have hlog := Real.log_nonneg hB
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hS : 0 ≤ D := Finset.sum_nonneg fun _ _ => by positivity
  have hpoint (i : ι) (hi : i ∈ s) :
      curveBound (δ i) B ≤ (δ i : ℝ) * U + (2 * Real.exp 1) * (δ i : ℝ) ^ 4 := by
    have hδ2 : (2 : ℝ) ≤ δ i := mod_cast hδ i hi
    have hδ0 : (0 : ℝ) < δ i := by linarith
    by_cases hsmall : (δ i : ℝ) ≤ Real.log B
    · have hpoly : (δ i : ℝ) ^ 3 ≤ 48 * Real.exp ((δ i : ℝ) / 2) := by
        have hh := Real.pow_div_factorial_le_exp ((δ i : ℝ) / 2) (by positivity) 3
        norm_num at hh; nlinarith
      have hexp : (δ i : ℝ) / 2 + Real.log B / δ i ≤ 1 + Real.log B / 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hsmall) (sub_nonneg.mpr hδ2),
          div_mul_cancel₀ (Real.log B) hδ0.ne']
      have hw : (δ i : ℝ) ^ 3 * B ^ (1 / (δ i : ℝ)) ≤ (48 * Real.exp 1) * B ^ (1 / 2 : ℝ) := calc
        _ ≤ (48 * Real.exp ((δ i : ℝ) / 2)) * B ^ (1 / (δ i : ℝ)) :=
          mul_le_mul_of_nonneg_right hpoly (by positivity)
        _ = 48 * Real.exp ((δ i : ℝ) / 2 + Real.log B / δ i) := by
          rw [Real.rpow_def_of_pos hB0, Real.exp_add, mul_assoc]; ring_nf
        _ ≤ 48 * Real.exp (1 + Real.log B / 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)
        _ = _ := by rw [Real.exp_add, Real.rpow_def_of_pos hB0, mul_assoc]; ring_nf
      have hc : curveBound (δ i) B ≤ U := by
        unfold curveBound
        exact (mul_le_mul hw (show Real.log B + δ i ≤ 2 * (Real.log B + 1) by linarith)
          (by positivity) (by positivity)).trans_eq (by dsimp [U]; ring)
      have hu : U ≤ (δ i : ℝ) * U := by
        simpa using mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ δ i) hU
      exact hc.trans (hu.trans (le_add_of_nonneg_right (by positivity)))
    · have hpow : B ^ (1 / (δ i : ℝ)) ≤ Real.exp 1 := by
        rw [Real.rpow_def_of_pos hB0]
        apply Real.exp_le_exp.mpr
        simpa only [mul_one_div] using (div_le_one hδ0).mpr (le_of_lt (lt_of_not_ge hsmall))
      have hc : curveBound (δ i) B ≤ (2 * Real.exp 1) * (δ i : ℝ) ^ 4 := by
        unfold curveBound
        exact (mul_le_mul (mul_le_mul_of_nonneg_left hpow (show 0 ≤ (δ i : ℝ) ^ 3 by positivity))
          (show Real.log B + δ i ≤ 2 * δ i by linarith) (by positivity)
          (show 0 ≤ (δ i : ℝ) ^ 3 * Real.exp 1 by positivity)).trans_eq (by ring)
      exact hc.trans (le_add_of_nonneg_left (by positivity))
  have hsum4 : ∑ i ∈ s, (δ i : ℝ) ^ 4 ≤ D ^ 4 := calc
    _ = ∑ i ∈ s, (δ i : ℝ) * (δ i : ℝ) ^ 3 := Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ ∑ i ∈ s, (δ i : ℝ) * D ^ 3 := Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _)
        (Finset.single_le_sum (fun _ _ => Nat.cast_nonneg _) hi) 3) (Nat.cast_nonneg _)
    _ = D ^ 4 := by rw [← Finset.sum_mul]; ring
  have hsplit : ∑ i ∈ s, curveBound (δ i) B ≤ D * U + (2 * Real.exp 1) * D ^ 4 := by
    refine (Finset.sum_le_sum hpoint).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum4 (by positivity))
  have hsmall_wt : B ^ (1 / Real.sqrt (d : ℝ)) * (B ^ (1 / 2 : ℝ) * (Real.log B + 1)) ≤ 5 * B := by
    have hlog' : B ^ (1 / 2 : ℝ) * (Real.log B + 1) ≤ 5 * B ^ (3 / 4 : ℝ) := by
      have hh := Real.rpow_half_mul_log_add_le (ε := (1 / 4 : ℝ)) (D := 1) hB
        (by norm_num) (by norm_num)
      norm_num at hh ⊢; exact hh
    have hexp : 1 / Real.sqrt (d : ℝ) + (3 / 4 : ℝ) ≤ 1 := by
      linarith [surface_inverse_sqrt_le_quarter hd]
    calc B ^ (1 / Real.sqrt (d : ℝ)) * (B ^ (1 / 2 : ℝ) * (Real.log B + 1))
      _ ≤ B ^ (1 / Real.sqrt (d : ℝ)) * (5 * B ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog' (by positivity)
      _ = 5 * B ^ (1 / Real.sqrt (d : ℝ) + 3 / 4) := by rw [Real.rpow_add hB0]; ring
      _ ≤ 5 * B := by
        simpa only [Real.rpow_one] using mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hB hexp) (show (0 : ℝ) ≤ 5 by norm_num)
  have hd0 : (0 : ℝ) < d := mod_cast (show 0 < d by omega)
  have hdp : (d : ℝ) ^ (9 / 2 : ℝ) ≤ (d : ℝ) ^ 18 := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ d by exact_mod_cast (show 1 ≤ d by omega)) (show (9 / 2 : ℝ) ≤ 18 by norm_num)
  have hsmall : D * U ≤ (480 * Real.exp 1) * C * (d : ℝ) ^ 18 * B := calc
    D * U ≤ (C * (d : ℝ) ^ (9 / 2 : ℝ) * B ^ (1 / Real.sqrt d)) * U :=
      mul_le_mul_of_nonneg_right hD hU
    _ = (96 * Real.exp 1) * C * (d : ℝ) ^ (9 / 2 : ℝ) *
        (B ^ (1 / Real.sqrt d) * (B ^ (1 / 2 : ℝ) * (Real.log B + 1))) := by dsimp [U]; ring
    _ ≤ (96 * Real.exp 1) * C * (d : ℝ) ^ (9 / 2 : ℝ) * (5 * B) :=
      mul_le_mul_of_nonneg_left hsmall_wt (by positivity)
    _ = (480 * Real.exp 1) * C * (d : ℝ) ^ (9 / 2 : ℝ) * B := by ring
    _ ≤ _ := by gcongr
  have hpow4 := pow_le_pow_left₀ hS hD 4
  rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hd0.le (9 / 2 : ℝ) 4,
    ← Real.rpow_mul_natCast hB0.le (1 / Real.sqrt d) 4] at hpow4
  norm_num only [show (9 / 2 : ℝ) * (4 : ℕ) = 18 by norm_num, Real.rpow_ofNat] at hpow4
  have hexp4 : (1 / Real.sqrt (d : ℝ)) * (4 : ℕ) ≤ (1 : ℝ) := by
    have := surface_inverse_sqrt_le_quarter hd; norm_num only [Nat.cast_ofNat]; linarith
  have hbox : B ^ ((1 / Real.sqrt (d : ℝ)) * (4 : ℕ)) ≤ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB hexp4
  have hlarge := mul_le_mul_of_nonneg_left
    (hpow4.trans (mul_le_mul_of_nonneg_left hbox (by positivity)))
    (show 0 ≤ 2 * Real.exp 1 by positivity)
  exact hsplit.trans ((add_le_add hsmall hlarge).trans_eq (by ring))

end
end CCDN
