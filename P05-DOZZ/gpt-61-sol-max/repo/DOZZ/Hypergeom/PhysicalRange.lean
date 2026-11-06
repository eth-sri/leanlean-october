/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Defs

/-! Physical parameter inequalities and Gamma coefficient positivity. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ.Proofs

/-- The strict four-point Seiberg range gives the ordered, nonresonant physical Gauss parameters.
-/
theorem gauss_physical_parameter_range (γ χ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hχ : χ = γ / 2 ∨ χ = 2 / γ)
    (hsum : 2 * Q γ + χ < α₁ + α₂ + α₃)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    0 < gaussParameterA γ χ α₁ α₂ α₃ ∧
      gaussParameterA γ χ α₁ α₂ α₃ < gaussParameterB γ χ α₁ α₂ α₃ ∧
      gaussParameterB γ χ α₁ α₂ α₃ < gaussParameterC γ χ α₁ ∧
      gaussParameterC γ χ α₁ < 1 ∧
      0 < gaussParameterC γ χ α₁ - gaussParameterA γ χ α₁ α₂ α₃ -
        gaussParameterB γ χ α₁ α₂ α₃ ∧
      gaussParameterC γ χ α₁ - gaussParameterA γ χ α₁ α₂ α₃ -
        gaussParameterB γ χ α₁ α₂ α₃ < 1 ∧
      0 < gaussK₁ (gaussParameterA γ χ α₁ α₂ α₃)
        (gaussParameterB γ χ α₁ α₂ α₃) (gaussParameterC γ χ α₁) ∧
      0 < gaussK₂ (gaussParameterA γ χ α₁ α₂ α₃)
        (gaussParameterB γ χ α₁ α₂ α₃) (gaussParameterC γ χ α₁) := by
  let A := gaussParameterA γ χ α₁ α₂ α₃
  let B := gaussParameterB γ χ α₁ α₂ α₃
  let C := gaussParameterC γ χ α₁
  
  have hχpos : 0 < χ := by
    continuity
  have hχQ : χ * Q γ = χ ^ 2 + 1 := by
    rcases hχ with hχ | hχ
    · rw [hχ]
      unfold Q
      field_simp
      ring
    · rw [hχ]
      unfold Q
      field_simp
  have hχQsub : χ * (Q γ - χ) = 1 := by linear_combination hχQ
  
  have hα₂χ : χ < α₂ := by linarith
  
  have hAform : A = χ / 2 * (α₁ + α₂ + α₃ - Q γ - 2 * χ) - 1 / 2 := by
    dsimp [A, gaussParameterA]
    ring
  have hAbase : χ / 2 * (Q γ - χ) - 1 / 2 = 0 := by linear_combination hχQ / 2
  have hA : 0 < A := by
    rw [hAform]
    calc
      0 = χ / 2 * (Q γ - χ) - 1 / 2 := hAbase.symm
      _ < χ / 2 * (α₁ + α₂ + α₃ - Q γ - 2 * χ) - 1 / 2 := by
        apply sub_lt_sub_right
        exact mul_lt_mul_of_pos_left (by linarith) (by positivity)
  have hBA : B - A = χ * (Q γ - α₃) := by
    dsimp [A, B, gaussParameterA, gaussParameterB]
    linear_combination (-1 : ℝ) * hχQ
  have hAB : A < B := by
    rw [← sub_pos, hBA]
    exact mul_pos hχpos (sub_pos.mpr hα₃)
  have hδeq : C - A - B = χ * (Q γ - α₂) := by
    dsimp [A, B, C, gaussParameterA, gaussParameterB, gaussParameterC]
    linear_combination (-1 : ℝ) * hχQ
  have hδpos : 0 < C - A - B := by
    simp_all
  have hδlt : C - A - B < 1 := by
    rw [hδeq]
    calc
      χ * (Q γ - α₂) < χ * (Q γ - χ) := by
        bound
      _ = 1 := hχQsub
  have hC1 : C < 1 := by
    dsimp [C, gaussParameterC]
    simp_all
  have hBC : B < C := by linarith
  have hCpos : 0 < C := by linarith
  have hCApos : 0 < C - A := by linarith
  have hCBpos : 0 < C - B := by linarith
  
  
  change 0 < A ∧ A < B ∧ B < C ∧ C < 1 ∧ 0 < C - A - B ∧
    C - A - B < 1 ∧ 0 < gaussK₁ A B C ∧ 0 < gaussK₂ A B C
  refine ⟨hA, hAB, hBC, hC1, hδpos, hδlt, ?_, ?_⟩
  · unfold gaussK₁
    
    
    
    
    have hgB := Real.Gamma_pos_of_pos (lt_trans hA hAB)
    positivity
  · unfold gaussK₂
    have hg2C := Real.Gamma_pos_of_pos (by linarith : 0 < 2 - C)
    have hg1A := Real.Gamma_pos_of_pos (by linarith : 0 < 1 - A)
    have hg1B := Real.Gamma_pos_of_pos (by linarith : 0 < 1 - B)
    have hgA1 := Real.Gamma_pos_of_pos (by linarith : 0 < A - C + 1)
    have hgB1 := Real.Gamma_pos_of_pos (by linarith : 0 < B - C + 1)
    positivity

end DOZZ.Proofs
