module
import Mathlib
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See third_party/twelfth/ATKINSON_SOURCE_TAIL_MANIFEST.json. Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonRootBand

@[expose] public section

/-!
# Cancellation outside the actual source-scale frequency band

The slope is controlled on the exact smooth source support, not the much
larger height-sized interval. Both signed carriers consume that geometry.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false



open Complex MeasureTheory Set

namespace MathCollab.Density.Stronger.Atkinson

theorem atkinsonRootSlope_outside_band {T G L b y : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    (hy : y ∈ Icc (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L))
    (hb : 6 * Real.sqrt T * (L / G) ≤ b) :
    b ≤ atkinsonRootSlope T b y ∧ atkinsonRootSlope T (-b) y ≤ -b := by
  have h := abs_le.mp (abs_atkinsonRootSlope_zero_le_band hT hG hL hwidth hy)
  have hp : atkinsonRootSlope T b y = atkinsonRootSlope T 0 y + 2 * b := by
    unfold atkinsonRootSlope
    ring
  have hn : atkinsonRootSlope T (-b) y = atkinsonRootSlope T 0 y - 2 * b := by
    unfold atkinsonRootSlope
    ring
  grind

theorem norm_atkinsonRootKernel_integral_outside_band {T G L b c : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    (hc : c ∈ Icc (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L))
    (hb : 6 * Real.sqrt T * (L / G) ≤ b) :
    ‖∫ y in atkinsonRootBandLower T G L..c, atkinsonRootKernel T b y‖ ≤ 1 / (b * Real.pi) ∧
      ‖∫ y in atkinsonRootBandLower T G L..c, atkinsonRootKernel T (-b) y‖ ≤
        1 / (b * Real.pi) := by
  have ha := atkinsonRootBandLower_pos hT G L
  have hb0 : 0 < b := (by positivity : 0 < 6 * Real.sqrt T * (L / G)).trans_le hb
  have hmem (y : ℝ) (hy : y ∈ Icc (atkinsonRootBandLower T G L) c) :
      y ∈ Icc (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L) :=
    ⟨hy.1, hy.2.trans hc.2⟩
  have hd (u y : ℝ) (hy : y ∈ Icc (atkinsonRootBandLower T G L) c) :
      deriv (atkinsonRootPhase T u) y = atkinsonRootSlope T u y :=
    (hasDerivAt_atkinsonRootPhase T u (ha.trans_le hy.1)).deriv
  have hmono (u : ℝ) : AntitoneOn (deriv (atkinsonRootPhase T u))
      (Icc (atkinsonRootBandLower T G L) c) := by
    intro x hx y hy hxy
    rw [hd u x hx, hd u y hy]
    exact (atkinsonRootSlope_strictAnti hT.le u).antitoneOn
      (ha.trans_le hx.1) (ha.trans_le hy.1) hxy
  constructor
  · exact norm_phaseIntegral_le_of_positive_slope hc.1 hb0
      (fun y hy => contDiffAt_atkinsonRootPhase T b (ha.trans_le hy.1))
      (fun y hy => by
        rw [hd b y hy]
        exact (atkinsonRootSlope_outside_band hT hG hL hwidth (hmem y hy) hb).1)
      (hmono b)
  · exact norm_phaseIntegral_le_of_negative_slope hc.1 hb0
      (fun y hy => contDiffAt_atkinsonRootPhase T (-b) (ha.trans_le hy.1))
      (fun y hy => by
        rw [hd (-b) y hy]
        exact (atkinsonRootSlope_outside_band hT hG hL hwidth (hmem y hy) hb).2)
      (hmono (-b))


