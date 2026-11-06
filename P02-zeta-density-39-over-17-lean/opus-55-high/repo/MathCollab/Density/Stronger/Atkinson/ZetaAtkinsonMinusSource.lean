module
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices and native assembly using revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1. See third_party/twelfth/ATKINSON_LOCAL_SOURCE_MANIFEST.json.
Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.ZetaAtkinsonReducedSource
public import MathCollab.Density.Stronger.Atkinson.AtkinsonMainIntegral
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# The actual physical source with only its oscillatory Y0 sum remaining

Both removed branches are paid for by proved bounds on their actual
complete integrals. The resulting source keeps the full divisor sum,
its normalization and one uniform logarithmic error constant.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Complex MeasureTheory

namespace MathCollab.Density.Stronger.Atkinson

theorem exists_zetaSquareLocalMean_le_atkinson_minus {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (zetaAtkinsonBesselMinus T G (Real.log T)).re +
          C * G * Real.log T := by
  pm_206 C hC B hB hsource exists_zetaSquareLocalMean_le_atkinson_reduced hδ
  pm_206 D hD B₁ hB₁ hmain exists_zetaAtkinsonVoronoiMain_log_bound hδ
  pm_4362
  pm_6117 hk hmain le_max_right
  pm_7440 zetaAtkinsonVoronoiMain
  pm_4360 hscaled hkr
  simp only [Complex.add_re] at hm
  nlinarith

end MathCollab.Density.Stronger.Atkinson
