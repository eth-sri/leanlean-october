module
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices and native assembly using revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1. See third_party/twelfth/ATKINSON_LOCAL_SOURCE_MANIFEST.json.
Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.ZetaAtkinsonMinusSource
public import MathCollab.Density.Stronger.Atkinson.ZetaNeumannSeries
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Actual zeta source with the two-term Neumann expansion

The full arithmetic replacement is consumed by the physical Gaussian
and local-mean theorems. All errors share one uniform logarithmic bound.
Stationary-phase evaluation of this oscillatory series remains separate.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Complex Filter MeasureTheory

namespace MathCollab.Density.Stronger.Atkinson

section
variable {δ : ℝ} (hδ : 0 < δ)
include δ hδ
theorem exists_zetaAtkinsonBesselMinus_twoTerm_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ‖zetaAtkinsonBesselMinus T G (Real.log T) -
        zetaAtkinsonTwoTermSum T G (Real.log T)‖ ≤ C * G * Real.log T := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaAtkinsonBesselMinus_sub_twoTerm_le
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ‖zetaAtkinsonBesselMinus T G (Real.log T) -
        zetaAtkinsonTwoTermSum T G (Real.log T)‖ ≤ C * G * Real.log T := by
    pm_4344
    apply (hbound T G (Real.log T) hsupport.1 hG
      (hscale.2.2 G hG hupper).1 hlog hwidth).trans
    exact le_mul_of_one_le_right (mul_nonneg hC.le hG.le) hscale.2.1
  pm_4343
  grind

theorem exists_zetaSquareLocalMean_le_atkinson_twoTerm :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (zetaAtkinsonTwoTermSum T G (Real.log T)).re +
          C * G * Real.log T := by
  pm_206 C hC B hB hsource exists_zetaSquareLocalMean_le_atkinson_minus hδ
  obtain ⟨D, hD, B₁, _, herror⟩ := exists_zetaAtkinsonBesselMinus_twoTerm_log_bound hδ
  pm_4362
  pm_6117 he herror le_max_right
  pm_5347 zetaAtkinsonBesselMinus zetaAtkinsonTwoTermSum
  pm_4360 hscaled hr
  nlinarith
end

end MathCollab.Density.Stronger.Atkinson
