module
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices and native assembly using revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1. See third_party/twelfth/ATKINSON_LOCAL_SOURCE_MANIFEST.json.
Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonK0Scales
public import MathCollab.Density.Stronger.Atkinson.ZetaAtkinsonVoronoi
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Phase-corrected physical source with the modified-Bessel branch removed

The genuine physical zeta source is now the full logarithmic main term
plus the oscillatory Neumann-kernel divisor sum, both using the
source's saddle-regulating integer-lattice phase. The discarded K0
branch is bounded by the proved complete-series power saving, not by
a separately supplied error hypothesis.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Complex Filter MeasureTheory

namespace MathCollab.Density.Stronger.Atkinson

theorem exists_zetaSquareLocalMean_le_atkinson_reduced {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (zetaAtkinsonVoronoiMain T G (Real.log T) +
          zetaAtkinsonBesselMinus T G (Real.log T)).re + C * G * Real.log T := by
  pm_206 C hC B hB hsource exists_zetaSquareLocalMean_le_atkinson_bessel hδ
  obtain ⟨B₁, hB₁, hplus⟩ := exists_zetaAtkinsonBesselPlus_powerSaving hδ 0
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (zetaAtkinsonVoronoiMain T G (Real.log T) +
          zetaAtkinsonBesselMinus T G (Real.log T)).re +
            (C + 2 * Real.exp 1) * G * Real.log T := by
    pm_4418
    intro G hlower hupper
    have hT0 : 0 < T := by grind
    pm_650 hG G Real.rpow_pos_of_pos hT0 δ hlower
    have hm := hsource T G hTB hG hupper
    have hk := hplus T G hTB₁ hlower hupper
    simp only [neg_zero, Real.rpow_zero, mul_one] at hk
    pm_7440 zetaAtkinsonBesselPlus
    pm_4360 hscaled hkr
    pm_4417
    pm_4360 herror hGlog
    simp only [Complex.add_re] at hm ⊢
    nlinarith
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hev
  refine ⟨C + 2 * Real.exp 1, by positivity, max 16 T₁, le_max_left _ _, ?_⟩
  intro T G hT hlower hupper
  grind

end MathCollab.Density.Stronger.Atkinson
