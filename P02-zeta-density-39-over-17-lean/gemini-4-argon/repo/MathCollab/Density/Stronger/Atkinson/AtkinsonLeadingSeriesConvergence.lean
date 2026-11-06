module
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Series algebra adapted from AtkinsonLeadingSeries at exact source revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, with native band convergence.
See third_party/twelfth/ATKINSON_LEADING_CONVERGENCE_MANIFEST.json.
Mathlib dependencies retain their Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonLeadingSeriesAlgebra
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSharpTruncation

@[expose] public section

noncomputable section
open Complex
namespace MathCollab.Density.Stronger.Atkinson

theorem exists_norm_tsum_zetaAtkinsonTwoTerm_sub_leading_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G →
        ‖(∑' n : ℕ, zetaAtkinsonTwoTerm T G L n) - atkinsonLeadingSum T G L‖ ≤ C * G := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_tsum_zetaAtkinsonTwoTerm_sub_leading_le_of_summable
  refine ⟨C, hC, ?_⟩
  intro T G L hT hG hGT hL hwidth
  exact hbound T G L hT (by linarith) hGT (by linarith) hwidth
    (summable_atkinsonLeadingTerm_of_band hT hG hGT hL hwidth)

