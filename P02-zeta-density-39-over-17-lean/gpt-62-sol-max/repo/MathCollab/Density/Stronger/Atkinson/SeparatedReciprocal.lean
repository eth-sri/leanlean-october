module
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm. See third_party/twelfth/ATKINSON_PACKET_MANIFEST.json and
third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonNearGap
public import GuthMaynard.NativeSource.GuthMaynard.SeparatedReciprocal

@[expose] public section

open Complex Finset Set Filter
open scoped ComplexConjugate
open RiemannZeta.GuthMaynard MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def IsSeparated (G : ℝ) (W : Finset ℝ) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, x ≠ y → G ≤ dist x y

theorem separated_annulus_card_le_two
    (W : Finset ℝ) (t : ℝ) (k : ℕ) (hSep : IsSeparated 1 W) :
    ({u ∈ W | u ≠ t ∧ (k : ℝ) ≤ |u - t| ∧ |u - t| < (k : ℝ) + 1}).card ≤ 2 :=
  GuthMaynard.NativeMoment.separated_annulus_card_le_two W t k hSep

theorem sum_inv_distance_near_le_harmonic
    (N : ℕ) (W : Finset ℝ) (t : ℝ) (hSep : IsSeparated 1 W) (ht : t ∈ W) :
    (∑ u ∈ {u ∈ W | u ≠ t ∧ |u - t| ≤ (N : ℝ)}, 1 / |u - t|) ≤
      2 * (((harmonic N : ℚ) : ℝ)) :=
  GuthMaynard.NativeMoment.sum_inv_distance_near_le_harmonic N W t hSep ht

end MathCollab.Density.Stronger.Atkinson
