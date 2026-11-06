/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Determinant.HypersurfaceLocalDeterminant
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Sharp leading term for the hypersurface local determinant exponent.
The linear error depends on dimension alone, not on singular multiplicity. -/

public section
namespace CCDN

/-- Optimize the binomial cutoff at the nonnegative mth root. -/
private theorem local_exponent_root_bound (m s e : ℕ) (hm : 0 < m)
    {μ : ℕ} (R : ℝ) (hR0 : 0 ≤ R)
    (hR : ↑μ * R ^ m = ↑m.factorial * s)
    (hcutoff : ∀ K : ℕ, s * K ≤ e + μ * (m + K).choose (m + 1)) :
    ↑s * R * m / (m + 1) ≤
      e + (m + 1 : ℝ) * s := by
  have hm1 : 0 < (m : ℝ) + 1 := by positivity
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hμ0 : (0 : ℝ) ≤ μ := Nat.cast_nonneg μ
  have hfac1 : (0 : ℝ) < (m + 1).factorial := by positivity
  by_cases hRm : ↑m ≤ R
  · let K := ⌊R⌋₊ - m
    have hmf := (Nat.le_floor_iff hR0).mpr hRm
    have hK : ↑K = (⌊R⌋₊ : ℝ) - m := Nat.cast_sub hmf
    have hupper : ↑m + K ≤ R := by linarith [Nat.floor_le hR0]
    have hlower : R - m - 1 ≤ ↑K := by linarith [Nat.lt_floor_add_one R]
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    have hcut := hcutoff K
    have hcutR : ↑s * K ≤ e +
        ↑μ * ((n + 1 + K).choose (n + 2) : ℝ) := by exact_mod_cast hcut
    have hb := Nat.choose_le_pow_div (α := ℝ) (n + 2) (n + 1 + K)
    have hpow : ((n + 1 + K : ℕ) : ℝ) ^ (n + 2) ≤ R ^ (n + 2) := by
      simp_all [pow_le_pow_left₀, Nat.cast_add,  Nat.cast_succ]
    have hb' := hb.trans (div_le_div_of_nonneg_right hpow (le_of_lt hfac1))
    have hfacEq : ((n + 2).factorial : ℝ) = ((n + 1 : ℕ) : ℝ) * (n + 1).factorial +
        (n + 1).factorial := by
      rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one]
      ring
    have hp : ↑μ * (R ^ (n + 2) / (n + 2).factorial) =
        ↑s * R / ((n + 1 : ℕ) + 1 : ℝ) := by
      grind
    have hpenalty := mul_le_mul_of_nonneg_left hb' hμ0
    rw [hp] at hpenalty
    have hlow := mul_le_mul_of_nonneg_left hlower hs0
    apply (div_le_iff₀ hm1).mpr
    have hmain' := (le_div_iff₀ hm1).mp
      (show ↑s * K - e ≤
        ↑s * R / ((n + 1 : ℕ) + 1 : ℝ) by linarith)
    nlinarith
  · have hsmall := le_of_lt (lt_of_not_ge hRm)
    have hprod := mul_le_mul_of_nonneg_left hsmall hs0
    apply (div_le_iff₀ hm1).mpr
    nlinarith

variable (m s e : ℕ) (hm : 0 < m) {μ : ℕ} (hμ : 0 < μ) (hcutoff : ∀ K : ℕ, s * K ≤ e + μ * (m + K).choose (m + 1))

include hm hμ hcutoff in
/-- The sharp multiplicity-dependent leading term, with a dimension-only
linear error. This is the numerical bound needed in CCDN Section 2. -/
private theorem local_exponent_lower_bound  :
    ↑s * ((↑m.factorial * s / μ) ^ (1 / (m : ℝ))) * m / (m + 1) ≤
      e + (m + 1 : ℝ) * s := by
  have hbase : 0 ≤ (m.factorial : ℝ) * s / μ := by positivity
  apply local_exponent_root_bound m s e hm _ (Real.rpow_nonneg hbase _) ?_ hcutoff
  rw [one_div, Real.rpow_inv_natCast_pow hbase (Nat.ne_of_gt hm)]
  field_simp

include hm hμ hcutoff in
/-- Under the binomial cutoff hypothesis, `(m!/μ)^(1/m) · m/(m+1) · s^(1+1/m) − (m+1)s ≤ e`:
the local exponent bound in the paper's separated-power notation. The error constant `m+1` is
uniform in both the equation and its multiplicity. -/
theorem local_exponent_separated_lower_bound  :
    (↑m.factorial / μ) ^ (1 / (m : ℝ)) * m / (m + 1) *
      ↑s ^ (1 + 1 / (m : ℝ)) - (m + 1 : ℝ) * s ≤
        e := by
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hb : 0 ≤ (m.factorial : ℝ) / μ := by positivity
  have hpower : ↑s ^ (1 + 1 / (m : ℝ)) = s * (s : ℝ) ^ (1 / (m : ℝ)) := by
    grind [Real.rpow_add', Real.rpow_one]
  have hsplit : ((↑m.factorial * s / μ) ^ (1 / (m : ℝ))) =
      (↑m.factorial / μ) ^ (1 / (m : ℝ)) * (s : ℝ) ^ (1 / (m : ℝ)) := by
    rw [show ↑m.factorial * s / μ = ((m.factorial : ℝ) / μ) * s by ring,
      Real.mul_rpow hb hs]
  have h := local_exponent_lower_bound m s e hm hμ hcutoff
  rw [hsplit] at h
  rw [hpower]
  convert (sub_le_iff_le_add.mpr h) using 1
  ring

/-- The local hypersurface profile satisfies the cutoff hypothesis in every
positive dimension. -/
lemma hypersurfaceMultiplicityExponent_cutoff_pos (m s K : ℕ) (hm : 0 < m)
    {μ : ℕ} (hμ : 0 < μ) :
    s * K ≤ hypersurfaceMultiplicityExponent m μ s + μ * (m + K).choose (m + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  exact hypersurfaceMultiplicityExponent_cutoff n s K hμ

/-- The sharp local estimate in the paper's separated-power notation. -/
theorem hypersurfaceMultiplicityExponent_lower_bound (m s : ℕ) (hm : 0 < m)
    {μ : ℕ} (hμ : 0 < μ) :
    (↑m.factorial / μ) ^ (1 / (m : ℝ)) * m / (m + 1) *
      ↑s ^ (1 + 1 / (m : ℝ)) - (m + 1 : ℝ) * s ≤
        hypersurfaceMultiplicityExponent m μ s :=
  local_exponent_separated_lower_bound m s _ hm hμ
    (fun K => hypersurfaceMultiplicityExponent_cutoff_pos m s K hm hμ)

end CCDN
