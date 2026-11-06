module
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm. See third_party/twelfth/ATKINSON_PACKET_MANIFEST.json and
third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonNearGap
public import Mathlib.NumberTheory.Harmonic.Bounds
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalLargeValues
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Finset Set Filter
open scoped ComplexConjugate
open RiemannZeta.GuthMaynard
open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def IsSeparated (G : ℝ) (W : Finset ℝ) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, x ≠ y → G ≤ dist x y

theorem separated_subset_card_le_one_of_diameter
    (W S : Finset ℝ) (hSep : IsSeparated 1 W) (hSW : S ⊆ W)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x - y| < 1) :
    S.card ≤ 1 := by
  pm_4795

export GuthMaynard.NativeMoment (sum_inv_distance_near_le_harmonic separated_annulus_card_le_two)

end MathCollab.Density.Stronger.Atkinson
