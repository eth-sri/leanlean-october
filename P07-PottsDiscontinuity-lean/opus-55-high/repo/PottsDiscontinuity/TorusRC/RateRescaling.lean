module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Absorbing a one-unit strip margin into a uniform crossing constant -/

public section

namespace PottsDiscontinuity.TorusRC

/-- Uniform rescaling for the source's polynomial block prefactor. -/
theorem block_rate_rescaling (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (m : ℕ) (hm : 0 < m) (M : ℝ) (hM : 0 ≤ M) :
    ((c^2/(9*Real.exp 2))/(9*((m+1:ℕ):ℝ)^2)) ^ (M/((m+1:ℕ):ℝ)) ≤
      (c/(9*(m:ℝ)^2)) ^ (M/(m:ℝ)) := by
  have hmR : (0:ℝ) < m := by positivity
  have hm1 : (1:ℝ) ≤ m := by aesop
  have hnR : (0:ℝ) < ((m+1:ℕ):ℝ) := by positivity
  have hl9 : 0 ≤ Real.log (9:ℝ) := by positivity
  have hlm := Real.log_le_sub_one_of_pos hmR
  have hlogs : Real.log (m:ℝ) ≤ Real.log ((m+1:ℕ):ℝ) :=
    Real.log_le_log hmR (by simp)
  have hla : Real.log ((c^2/(9*Real.exp 2))/(9*((m+1:ℕ):ℝ)^2)) =
      2*Real.log c - 2*Real.log 9 - 2 - 2*Real.log ((m+1:ℕ):ℝ) := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity), Real.log_pow,
      Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    ring
  have hlb : Real.log (c/(9*(m:ℝ)^2)) =
      Real.log c - Real.log 9 - 2*Real.log (m:ℝ) := by
    rw [Real.log_div hc.ne' (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    ring
  have hcross :
      Real.log ((c^2/(9*Real.exp 2))/(9*((m+1:ℕ):ℝ)^2)) * (m:ℝ) ≤
      Real.log (c/(9*(m:ℝ)^2)) * ((m+1:ℕ):ℝ) := by
    rw [hla,hlb,Nat.cast_add,Nat.cast_one]
    have h₁ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hm1) (Real.log_nonpos hc.le hc1)
    have h₂ := mul_nonneg (sub_nonneg.mpr hm1) hl9
    have h₃ := mul_nonneg hmR.le (sub_nonneg.mpr hlogs)
    grind
  rw [Real.rpow_def_of_pos (by positivity),Real.rpow_def_of_pos (by positivity)]
  apply Real.exp_le_exp.mpr
  convert mul_le_mul_of_nonneg_left ((div_le_div_iff₀ hnR hmR).mpr hcross) hM using 1 <;> ring

end PottsDiscontinuity.TorusRC
