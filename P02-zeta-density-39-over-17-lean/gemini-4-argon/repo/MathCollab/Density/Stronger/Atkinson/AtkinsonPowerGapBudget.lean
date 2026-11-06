module
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm. See third_party/twelfth/ATKINSON_PACKET_MANIFEST.json and
third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonLocalizedPowers

@[expose] public section

open Complex Finset Set Filter RiemannZeta.GuthMaynard MathCollab.Density.Stronger.Fourth
open scoped ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem atkinson_harmonic_mono {m n : ℕ} (hmn : m ≤ n) :
    (harmonic m:ℝ) ≤ (harmonic n:ℝ) := by
  unfold harmonic
  push_cast
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun _ _ _ => by positivity)






