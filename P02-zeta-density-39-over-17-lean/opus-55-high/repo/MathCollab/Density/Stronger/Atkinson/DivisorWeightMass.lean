module
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.DivisorWeightVariation
import WeylPort.Analytic.RealLaplace

public section

open Complex Filter MeasureTheory Topology
open MathCollab.Density.Stronger.Fourth
open scoped Interval ComplexConjugate
namespace MathCollab.Density.Stronger.Atkinson


theorem min_one_le_rpow {a θ : ℝ} (ha : 0 ≤ a) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    min 1 a ≤ a ^ θ := by
  by_cases ha1 : a ≤ 1
  · rw [min_eq_right ha1]
    exact Real.self_le_rpow_of_le_one ha ha1 hθ1
  · rw [min_eq_left (le_of_not_ge ha1)]
    exact Real.one_le_rpow (le_of_not_ge ha1) hθ

theorem norm_divisorCritical_mul_ratio_rpow {A : ℝ} (hA : 0 < A)
    (t θ : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖divisorDirichletTerm (afeCriticalPoint t) n‖ * (A / (n : ℝ)) ^ θ =
      A ^ θ * ‖divisorDirichletTerm ((1 / 2 + θ : ℝ) : ℂ) n‖ := by
  pm_456 hnR n hn
  simp only [divisorDirichletTerm, LSeries.norm_term_eq, hn.ne', ite_false,
    afeCriticalPoint, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_zero, add_zero]
  norm_num only [div_ofNat_re, one_re]
  rw [Real.div_rpow hA.le hnR.le, Real.rpow_add hnR]
  ring

theorem norm_divisorCritical_mul_min_le {A θ : ℝ} (hA : 0 < A)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (t : ℝ) (n : ℕ) :
    ‖divisorDirichletTerm (afeCriticalPoint t) n‖ * min 1 (A / (n : ℝ)) ≤
      A ^ θ * ‖divisorDirichletTerm ((1 / 2 + θ : ℝ) : ℂ) n‖ := by
  pm_4346
  calc
    _ ≤ ‖divisorDirichletTerm (afeCriticalPoint t) n‖ * (A / (n : ℝ)) ^ θ :=
      mul_le_mul_of_nonneg_left (min_one_le_rpow (by positivity) hθ hθ1) (norm_nonneg _)
    _ = _ := norm_divisorCritical_mul_ratio_rpow hA t θ (Nat.pos_of_ne_zero hn)

section
variable {A θ : ℝ} (hA : 0 < A) (hθ : 1 / 2 < θ) (hθ1 : θ ≤ 1) (t : ℝ)
include A θ hA hθ hθ1 t
theorem summable_divisorCritical_min :
    Summable (fun n : ℕ => ‖divisorDirichletTerm (afeCriticalPoint t) n‖ * min 1 (A / (n : ℝ))) := by
  pm_4347
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (norm_divisorCritical_mul_min_le hA (by linarith) hθ1 t) (hs.mul_left (A ^ θ))

theorem tsum_divisorCritical_min_le :
    (∑' n : ℕ, ‖divisorDirichletTerm (afeCriticalPoint t) n‖ * min 1 (A / (n : ℝ))) ≤
      A ^ θ * ∑' n : ℕ, ‖divisorDirichletTerm ((1 / 2 + θ : ℝ) : ℂ) n‖ := by
  pm_4347
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (norm_divisorCritical_mul_min_le hA (by linarith) hθ1 t)
    (summable_divisorCritical_min hA hθ hθ1 t) (hs.mul_left (A ^ θ))
end

theorem summable_norm_source_divisor_weight {T : ℝ} (hT : 0 < T) (t : ℝ) :
    Summable (fun n : ℕ => ‖divisorDirichletTerm (afeCriticalPoint t) n‖ *
      ‖zetaDivisorWeight (zetaDivisorWeightArgument T n)‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_source_zetaDivisorWeight_min_le
  have hs := (summable_divisorCritical_min (A := T / (2 * Real.pi)) (θ := 3 / 4)
    (by positivity) (by norm_num) (by norm_num) t).mul_left C
  apply Summable.of_nonneg_of_le (fun n => by positivity) ?_ hs
  intro n
  pm_4346
  pm_5612 hT
  pm_99 div_div mul_assoc mul_comm mul_left_comm h

section
variable (ε : ℝ) (hε : 0 < ε)
include ε hε
/-- A single constant for all heights and all oscillatory phases of the
critical-line divisor coefficient. The loss is arbitrarily small. -/
theorem exists_tsum_norm_source_divisor_weight_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ t : ℝ,
      (∑' n : ℕ, ‖divisorDirichletTerm (afeCriticalPoint t) n‖ *
        ‖zetaDivisorWeight (zetaDivisorWeightArgument T n)‖) ≤ C * T ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_source_zetaDivisorWeight_min_le
  pm_4348
  pm_7546
  intro T hT t
  have hT0 : 0 < T := by linarith
  have hpoint (n : ℕ) : ‖divisorDirichletTerm (afeCriticalPoint t) n‖ *
      ‖zetaDivisorWeight (zetaDivisorWeightArgument T n)‖ ≤
      C * (‖divisorDirichletTerm (afeCriticalPoint t) n‖ * min 1 ((T / (2 * Real.pi)) / (n : ℝ))) := by
    pm_4346
    pm_5612 hT0
    pm_99 div_div mul_assoc mul_comm mul_left_comm h
  have hsum := Summable.tsum_le_tsum hpoint (summable_norm_source_divisor_weight hT0 t)
    ((summable_divisorCritical_min (by positivity) hθ hθ1 t).mul_left C)
  rw [tsum_mul_left] at hsum
  apply hsum.trans
  pm_1586
  pm_4349
  calc
    _ ≤ C * ((T / (2 * Real.pi)) ^ θ * S) := mul_le_mul_of_nonneg_left hm hC.le
    _ ≤ C * (T ^ (1 / 2 + ε) * S) := by gcongr
    _ ≤ _ := by nlinarith [Real.rpow_nonneg hT0.le (1 / 2 + ε)]

/-- The comparison mass itself has the same square-root scale. It can
therefore control weight differences without needing any lower bound on
the complex weight, which can have cancellation. -/
theorem exists_tsum_divisorCritical_min_height_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ t : ℝ,
      (∑' n : ℕ, ‖divisorDirichletTerm (afeCriticalPoint t) n‖ *
        min 1 (T / (2 * Real.pi * (n : ℝ)))) ≤ C * T ^ (1 / 2 + ε) := by
  pm_4348
  refine ⟨1 + S, by positivity, ?_⟩
  intro T hT t
  have hT0 : 0 < T := by linarith
  pm_1586
  simp only [div_div] at hm
  pm_4349
  apply hm.trans
  calc
    _ ≤ T ^ (1 / 2 + ε) * S := mul_le_mul_of_nonneg_right hpow hS
    _ ≤ _ := by nlinarith [Real.rpow_nonneg hT0.le (1 / 2 + ε)]
end

end MathCollab.Density.Stronger.Atkinson
