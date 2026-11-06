module
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm. See third_party/twelfth/ATKINSON_PACKET_MANIFEST.json and
third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonLocalizedGapBudget

@[expose] public section

open Complex Finset Set Filter RiemannZeta.GuthMaynard MathCollab.Density.Stronger.Fourth
open scoped ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson


theorem atkinson_weighted_diagonal_power {M : ℝ} (hM : 0 < M) (η : ℝ) :
    M^(1/2+η)*M = M^(3/2+η) := by
  calc
    _ = M^(1/2+η)*M^(1:ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hM]; congr 1; ring

theorem atkinson_weighted_near_power {H M : ℝ} (hH : 0 < H) (hM : 0 < M) (η : ℝ) :
    M^(1/2+η)*Real.sqrt (H*M) = Real.sqrt H*M^(1+η) := by
  rw [Real.sqrt_mul hH.le,Real.sqrt_eq_rpow M]
  calc
    _ = Real.sqrt H*(M^(1/2+η)*M^(1/2:ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hM]; congr 1; congr 1; ring

