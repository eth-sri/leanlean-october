module
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm. See third_party/twelfth/ATKINSON_PACKET_MANIFEST.json and
third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonGapBudget

@[expose] public section

open Complex Finset Set Filter RiemannZeta.GuthMaynard MathCollab.Density.Stronger.Fourth
open scoped ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson


theorem atkinson_quarter_energy_power {x : ℝ} (hx : 0 < x) (η : ℝ) :
    (x^(-(1/4:ℝ)))^2*x^(1+η) = x^(1/2+η) := by
  rw [sq,← Real.rpow_add hx,← Real.rpow_add hx]
  congr 1
  ring


