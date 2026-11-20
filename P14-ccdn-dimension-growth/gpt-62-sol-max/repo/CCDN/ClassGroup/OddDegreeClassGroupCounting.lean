/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.AffineHypersurfaceAuxiliary
public import CCDN.ClassGroup.NumberFieldLatticeBox
import CCDN.ClassGroup.OddDegreeNormCurveCount
import CCDN.ClassGroup.NormCurveReduction

/-! The odd-degree class-group counting step uses the finite
translation classes and their two signed norm curves. The curve equation
retains its full odd degree, including when the translating generator
belongs to a proper subfield. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField NumberField.InfinitePlace

/-- For `n ≥ 2` and `B ≥ 1`, the norm-curve box height `H = max (2 * B) (√(B ^ n))` satisfies
`H ^ (1 / n) ≤ 2 * √B`. -/
lemma normCurveBoxHeight_root_le {n : ℕ} (hn : 2 ≤ n) {B : ℝ} (hB : 1 ≤ B) :
    (max (2 * B) (Real.sqrt (B ^ n))) ^ (1 / (n : ℝ)) ≤ 2 * Real.sqrt B := by
  have hB0 := zero_le_one.trans hB
  have hs : 1 ≤ Real.sqrt B := by
    simp_all
  have hbase : 1 ≤ 2 * Real.sqrt B := by linarith
  have hsquare : (2 * Real.sqrt B) ^ 2 = 4 * B := by
    grind
  have hpower : (2 * Real.sqrt B) ^ 2 ≤ (2 * Real.sqrt B) ^ n :=
    pow_le_pow_right₀ hbase hn
  have hH : max (2 * B) (Real.sqrt (B ^ n)) ≤ (2 * Real.sqrt B) ^ n := by
    apply max_le
    linarith
    · apply (Real.sqrt_le_left (pow_nonneg (by positivity) _)).mpr
      calc
        B ^ n ≤ ((2 * Real.sqrt B) ^ 2) ^ n :=
          pow_le_pow_left₀ hB0 (by linarith) n
        _ = ((2 * Real.sqrt B) ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm n 2]
  have hh := Real.rpow_le_rpow (by positivity) hH (by positivity : 0 ≤ 1 / (n : ℝ))
  rw [one_div, Real.pow_rpow_inv_natCast (by positivity) (by omega)] at hh
  simp_all

variable (K : Type*) [Field K] [NumberField K]

/-- Summing over the constructed curves costs two signs and a factor
`2 √B` from their square-height parameter. -/
theorem boundedSquareNormIntegers_odd_count (hn : 2 ≤ Module.finrank ℚ K) (hodd : Odd (Module.finrank ℚ K))
    {B : ℝ} (hB : 1 ≤ B) :
    ((boundedSquareNormIntegers K B).ncard : ℝ) ≤
      (12 * affineHypersurfaceAuxiliaryConstant 0 * (Module.finrank ℚ K : ℝ) ^ 4) *
        (boundedSquareNormTranslationClasses K B).card * Real.sqrt B := by
  let n := Module.finrank ℚ K
  let A := 3 * affineHypersurfaceAuxiliaryConstant 0 * (n : ℝ) ^ 4
  have hA : 0 ≤ A := by have := affineHypersurfaceAuxiliaryConstant_pos 0; positivity
  have hh := squareNorm_count_le_of_curves K (C := A * (2 * Real.sqrt B)) (by positivity)
    ∅ Set.finite_empty (fun _ => True) (by simp) (fun β ε _ hε =>
      (signed_norm_curve_log_free_count K β hε hn hodd ((show 1 ≤ 2 * B by linarith).trans (le_max_left _ _))).trans
        (mul_le_mul_of_nonneg_left (normCurveBoxHeight_root_le hn hB) hA))
  convert hh using 1
  simp [A, n]
  ring

end
end CCDN
