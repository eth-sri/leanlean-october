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
  have hmR : (2 : ℝ) ≤ m := mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  let ε : ℝ := 1 / (4 * (m : ℝ))
  have hhalf : 0 < ε / 2 := by dsimp only [ε]; positivity
  obtain ⟨A₀, hA₀, hprime⟩ := two_pow_primeFactors_subpower (4 * m) hhalf
  let L : ℝ := ((2 : ℕ).factorial : ℝ) / (ε / 2) ^ 2 * Real.exp (ε / 2)
  have hL : 0 < L := by dsimp only [L]; positivity
  let A := A₀ * L
  have hA : 0 < A := mul_pos hA₀ hL
  refine ⟨C ^ 2 * (2 : ℝ) ^ (2 * m) * A, by positivity, fun D hD x h H hx hxD hh hbound hH => ?_⟩
  have hDR : (1 : ℝ) ≤ D := mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hx0 : 0 < x := by linarith
  have hxD' : x ≤ (D : ℝ) := by nlinarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogD : Real.log x ≤ Real.log (D : ℝ) := Real.log_le_log hx0 hxD'
  let α : ℝ := 1 / 2 - 1 / (2 * (m : ℝ))
  have hα : 0 ≤ α := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ 2 * (m : ℝ) by linarith)
    dsimp only [α]; linarith
  have hgeom : (x ^ α) ^ 2 ≤ (D : ℝ) ^ α := by
    rw [Real.rpow_pow_comm hx0.le]; exact Real.rpow_le_rpow (sq_nonneg x) hxD hα
  have hlogs : (Real.log x + 1) ^ 2 ≤ (Real.log (D : ℝ) + 1) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  let P : ℝ := (2 : ℝ) ^ ((2 * m) * D.primeFactors.card + m)
  have hP : P ^ 2 = (2 : ℝ) ^ (2 * m) * (2 : ℝ) ^ ((4 * m) * D.primeFactors.card) := by
    dsimp only [P]; rw [← pow_mul, ← pow_add]; congr 1; ring
  have hmain : C ^ 2 * (x ^ α) ^ 2 * (Real.log x + 1) ^ 2 ≤
      C ^ 2 * (D : ℝ) ^ α * (Real.log (D : ℝ) + 1) ^ 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_left hgeom (sq_nonneg C)) hlogs
      (sq_nonneg _) (by positivity)
  have hweight : (2 : ℝ) ^ ((4 * m) * D.primeFactors.card) * (Real.log (D : ℝ) + 1) ^ 2 ≤
      A * (D : ℝ) ^ ε := by
    have hlog := logarithm_add_one_pow_le_rpow 2 hhalf hDR
    change (Real.log (D : ℝ) + 1) ^ 2 ≤ L * (D : ℝ) ^ (ε / 2) at hlog
    exact (mul_le_mul (hprime D hD) hlog (by positivity) (by positivity)).trans_eq (by
      rw [show (D : ℝ) ^ ε = (D : ℝ) ^ (ε / 2) * (D : ℝ) ^ (ε / 2) by
        rw [← Real.rpow_add hD0]; congr 1; ring]; dsimp [A]; ring)
  have hexponent : α + ε = 1 / 2 - 1 / (2 * ((2 * m : ℕ) : ℝ)) := by
    dsimp only [α, ε]; push_cast; field_simp; ring
  calc
    H ≤ (h * P) ^ 2 := hH
    _ ≤ ((C * x ^ α * (Real.log x + 1)) * P) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hh (by positivity))
        (mul_le_mul_of_nonneg_right hbound (by positivity)) 2
    _ = (C ^ 2 * (x ^ α) ^ 2 * (Real.log x + 1) ^ 2) * P ^ 2 := by ring
    _ ≤ (C ^ 2 * (D : ℝ) ^ α * (Real.log (D : ℝ) + 1) ^ 2) * P ^ 2 :=
      mul_le_mul_of_nonneg_right hmain (sq_nonneg P)
    _ = (C ^ 2 * (2 : ℝ) ^ (2 * m)) * (D : ℝ) ^ α *
        ((2 : ℝ) ^ ((4 * m) * D.primeFactors.card) * (Real.log (D : ℝ) + 1) ^ 2) := by
      rw [hP]; ring
    _ ≤ (C ^ 2 * (2 : ℝ) ^ (2 * m)) * (D : ℝ) ^ α * (A * (D : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left hweight (by positivity)
    _ = (C ^ 2 * (2 : ℝ) ^ (2 * m) * A) *
        (D : ℝ) ^ (1 / 2 - 1 / (2 * ((2 * m : ℕ) : ℝ))) := by
      rw [← hexponent, Real.rpow_add hD0]; ring

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
  norm_num
  nlinarith [hbound D hD]

end
end CCDN
