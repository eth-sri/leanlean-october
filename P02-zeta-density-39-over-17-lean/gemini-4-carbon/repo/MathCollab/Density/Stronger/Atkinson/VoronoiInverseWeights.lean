module
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.VoronoiTest
public import Mathlib.Analysis.MellinInversion

@[expose] public section

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff Topology
open Classical
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

noncomputable def dfiVoronoiInvWeight (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x : ℂ)⁻¹ * g x

/-- Repeated multiplication by the inverse source variable.  This is the
Mellin-coordinate implementation of the repeated integration by parts used
to truncate the Bessel transforms in DFI equation (29). -/
noncomputable def dfiVoronoiInvWeightIterate :
    ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, g => g
  | k + 1, g => dfiVoronoiInvWeight (dfiVoronoiInvWeightIterate k g)

@[simp]
theorem dfiVoronoiInvWeightIterate_zero (g : ℝ → ℂ) :
    dfiVoronoiInvWeightIterate 0 g = g := rfl

@[simp]
theorem dfiVoronoiInvWeightIterate_succ (k : ℕ) (g : ℝ → ℂ) :
    dfiVoronoiInvWeightIterate (k + 1) g =
      dfiVoronoiInvWeight (dfiVoronoiInvWeightIterate k g) := rfl

end MathCollab.Density.Stronger.Atkinson
