/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Analysis.SmallDegreeSurfaceNumerics
import CCDN.ClassGroup.PrimeFactorSubpower

/-! Uniform numerical absorption for quadratic class-group descent.
The prime-factor and logarithmic losses fit in the positive exponent
margin between the base-field and extension-field estimates. -/

@[expose] public section
namespace CCDN
noncomputable section

private theorem primeFactors_polylog_subpower (a k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 1 ≤ D →
      (2 : ℝ) ^ (a * D.primeFactors.card) * (Real.log (D : ℝ) + 1) ^ k ≤
        C * (D : ℝ) ^ ε := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨A, hA, hprime⟩ := two_pow_primeFactors_subpower a hhalf
  let L := logarithmicBoxConstant k (ε / 2)
  refine ⟨A * L, mul_pos hA (by unfold L logarithmicBoxConstant; positivity), ?_⟩
  intro D hD
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := by linarith
  have hlog := logarithm_add_one_pow_le_rpow k hhalf hDR
  change (Real.log (D : ℝ) + 1) ^ k ≤ L * (D : ℝ) ^ (ε / 2) at hlog
  calc
    _ ≤ (A * (D : ℝ) ^ (ε / 2)) * (L * (D : ℝ) ^ (ε / 2)) :=
      mul_le_mul (hprime D hD) hlog (by positivity) (by positivity)
    _ = (A * L) * (D : ℝ) ^ ε := by
      calc
        _ = (A * L) * ((D : ℝ) ^ (ε / 2) * (D : ℝ) ^ (ε / 2)) := by ring
        _ = _ := by rw [← Real.rpow_add hDpos, add_halves]

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
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  
  let ε : ℝ := 1 / (4 * (m : ℝ))
  have hε : 0 < ε := by positivity
  obtain ⟨A, hA, hweight⟩ := primeFactors_polylog_subpower (4 * m) 2 hε
  refine ⟨C ^ 2 * (2 : ℝ) ^ (2 * m) * A, by positivity, ?_⟩
  intro D hD x h H hx hxD hh hbound hH
  have hD0 : (0 : ℝ) < D := by positivity
  have hx0 : 0 < x := by linarith
  have hlog := Real.log_le_log hx0 (show x ≤ (D : ℝ) by nlinarith)
  have hlogx := Real.log_nonneg hx
  let α : ℝ := 1 / 2 - 1 / (2 * (m : ℝ))
  have hα : 0 ≤ α := sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num) (by linarith))
  have hgeom : (x ^ α) ^ 2 ≤ (D : ℝ) ^ α := by
    rw [Real.rpow_pow_comm hx0.le]
    gcongr
  have hexponent : α + ε = 1 / 2 - 1 / (2 * ((2 * m : ℕ) : ℝ)) := by grind
  calc
    H ≤ (C * x ^ α * (Real.log x + 1) * (2 : ℝ) ^ ((2 * m) * D.primeFactors.card + m)) ^ 2 :=
      hH.trans (by gcongr)
    _ = (C ^ 2 * (2 : ℝ) ^ (2 * m)) * (x ^ α) ^ 2 *
        ((2 : ℝ) ^ ((4 * m) * D.primeFactors.card) * (Real.log x + 1) ^ 2) := by ring
    _ ≤ (C ^ 2 * (2 : ℝ) ^ (2 * m)) * (D : ℝ) ^ α * (A * (D : ℝ) ^ ε) := by
      gcongr 1
      · gcongr
      · exact (mul_le_mul_of_nonneg_left (by gcongr) (by positivity)).trans (hweight D hD)
    _ = _ := by rw [← hexponent, Real.rpow_add hD0]; ring

/-- The explicit quadratic-field genus bound already implies the
degree-two power bound needed to start degree induction. -/
theorem quadratic_class_group_base_numeric :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 1 ≤ D →
      (2 : ℝ) ^ (4 * D.primeFactors.card + 2) ≤ C * (D : ℝ) ^ (1 / 4 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := two_pow_primeFactors_subpower 4
    (by norm_num : (0 : ℝ) < 1 / 4)
  refine ⟨4 * C, by positivity, ?_⟩
  intro D hD
  rw [pow_add]
  grind

end
end CCDN
