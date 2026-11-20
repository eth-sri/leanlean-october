/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.HypersurfaceLocalDeterminant
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Sharp leading term for the hypersurface local determinant exponent.
The linear error depends on dimension alone, not on singular multiplicity. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- Optimize the binomial cutoff at the nonnegative mth root. -/
private theorem local_exponent_root_bound (m s e : ℕ) (hm : 0 < m)
    {μ : ℕ} (R : ℝ) (hR0 : 0 ≤ R)
    (hR : (μ : ℝ) * R ^ m ≤ (m.factorial : ℝ) * s)
    (hcutoff : ∀ K : ℕ, s * K ≤ e + μ * (m + K).choose (m + 1)) :
    (s : ℝ) * R * m / (m + 1) ≤
      e + (m + 1 : ℝ) * s := by

  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hμ0 : (0 : ℝ) ≤ μ := Nat.cast_nonneg μ

  by_cases hRm : (m : ℝ) ≤ R
  · let K : ℕ := ⌊R⌋₊ - m
    have hmf := (Nat.le_floor_iff hR0).mpr hRm
    have hK : (K : ℝ) = (⌊R⌋₊ : ℝ) - m := Nat.cast_sub hmf
    have hupper : (m : ℝ) + K ≤ R := by linarith [Nat.floor_le hR0]
    have hlower : R - m - 1 ≤ (K : ℝ) := by linarith [Nat.lt_floor_add_one R]
    have hcut : (s : ℝ) * K ≤ e + (μ : ℝ) * ((m + K).choose (m + 1) : ℝ) := by
      exact_mod_cast hcutoff K
    have hb := (Nat.choose_le_pow_div (α := ℝ) (m + 1) (m + K)).trans
      (by gcongr; exact_mod_cast hupper : ((m + K : ℕ) : ℝ) ^ (m + 1) / (m + 1).factorial ≤
          R ^ (m + 1) / (m + 1).factorial)
    have hp : (μ : ℝ) * (R ^ (m + 1) / (m + 1).factorial) ≤ s * R / (m + 1) := by
      rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      have h := mul_le_mul_of_nonneg_right hR hR0
      apply (le_div_iff₀ hm1).2

      field_simp
      nlinarith only [h]
    have hmain := (hcut.trans (add_le_add le_rfl ((mul_le_mul_of_nonneg_left hb hμ0).trans hp)))
    have hlow := mul_le_mul_of_nonneg_left hlower hs0
    apply (div_le_iff₀ hm1).mpr
    field_simp at hmain
    nlinarith only [hmain, mul_le_mul_of_nonneg_right hlow hm1.le]
  · have hsmall : R ≤ m := le_of_lt (lt_of_not_ge hRm)
    have hprod := mul_le_mul_of_nonneg_left hsmall hs0
    apply (div_le_iff₀ hm1).mpr
    have hsr : 0 ≤ (s : ℝ) * R := mul_nonneg hs0 hR0
    nlinarith

/-- The binomial cutoff bound with an upper bound `Q` for the multiplicity root. -/
theorem local_exponent_separated_lower_bound (m s e : ℕ) (hm : 0 < m) {μ : ℕ} (hμ : 0 < μ)
    {Q : ℝ} (hQ : (μ : ℝ) ^ (1 / (m : ℝ)) ≤ Q)
    (hcutoff : ∀ K : ℕ, s * K ≤ e + μ * (m + K).choose (m + 1)) :
    ((m.factorial : ℝ) ^ (1 / (m : ℝ)) * m / (m + 1) *
      (s : ℝ) ^ (1 + 1 / (m : ℝ))) / Q - (m + 1 : ℝ) * s ≤ e := by
  have hμ0 : (0 : ℝ) < μ := by positivity
  have hQ0 := (Real.rpow_pos_of_pos hμ0 _).trans_le hQ
  let R := ((m.factorial : ℝ) * s) ^ (1 / (m : ℝ)) / Q
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hrpow (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / (m : ℝ))) ^ m = x := by
    rw [one_div, Real.rpow_inv_natCast_pow hx hm.ne']
  have hμQ := pow_le_pow_left₀ (Real.rpow_nonneg hμ0.le _) hQ m
  rw [hrpow _ hμ0.le] at hμQ
  have hR : (μ : ℝ) * R ^ m ≤ (m.factorial : ℝ) * s := calc
    _ ≤ Q ^ m * R ^ m := by gcongr
    _ = _ := by
      have he : Q * R = ((m.factorial : ℝ) * s) ^ (1 / (m : ℝ)) := by dsimp [R]; field_simp
      rw [← mul_pow, he, hrpow _ (by positivity)]
  have h := local_exponent_root_bound m s e hm R hR0 hR hcutoff
  rw [Real.rpow_add' (Nat.cast_nonneg s) (by positivity), Real.rpow_one]
  dsimp only [R] at h
  rw [Real.mul_rpow (by positivity) (by positivity)] at h
  convert sub_le_iff_le_add.mpr h using 1
  ring

/-- The local hypersurface profile satisfies the cutoff hypothesis in every
positive dimension. -/
lemma hypersurfaceMultiplicityExponent_cutoff_pos (m s K : ℕ) (hm : 0 < m)
    {μ : ℕ} (hμ : 0 < μ) :
    s * K ≤ hypersurfaceMultiplicityExponent m μ s + μ * (m + K).choose (m + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  exact hypersurfaceMultiplicityExponent_cutoff n s K hμ

/-- The smooth local estimate (multiplicity one). -/
theorem hypersurfaceMultiplicityExponent_lower_bound (m s : ℕ) (hm : 0 < m) :
    (m.factorial : ℝ) ^ (1 / (m : ℝ)) * m / (m + 1) *
      (s : ℝ) ^ (1 + 1 / (m : ℝ)) - (m + 1 : ℝ) * s ≤
        hypersurfaceMultiplicityExponent m 1 s := by
  simpa using local_exponent_separated_lower_bound m s _ hm (μ := 1) one_pos (Q := 1)
    (by simp) (fun K => hypersurfaceMultiplicityExponent_cutoff_pos m s K hm one_pos)

end
end CCDN
