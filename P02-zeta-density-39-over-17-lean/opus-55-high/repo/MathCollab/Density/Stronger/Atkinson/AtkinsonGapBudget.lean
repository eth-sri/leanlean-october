module
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm. See third_party/twelfth/ATKINSON_PACKET_MANIFEST.json and
third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonDyadicGramBudget

@[expose] public section

open Complex Finset Set Filter
open scoped ComplexConjugate
open RiemannZeta.GuthMaynard
open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonDyadicGapBudget (N : ℕ) (W : Finset ℝ) : ℝ :=
  (Nat.clog 2 N : ℝ)*∑ j ∈ Finset.range (Nat.clog 2 N),
    (((2^j:ℕ):ℝ)^(-(1/4:ℝ)))^2*atkinsonBlockCoefficientEnergy (2^j) (2^j)*
      ∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGapMajorant (2^j) (2^j) t u

theorem atkinsonDyadicGramBudget_le_gapBudget (N : ℕ) (W : Finset ℝ)
    (hgap : ∀ j < Nat.clog 2 N, ∀ t ∈ W, ∀ u ∈ W,
      atkinsonPrefixGramMax (2^j) (2^j) t u ≤ atkinsonPrefixGapMajorant (2^j) (2^j) t u) :
    atkinsonDyadicGramBudget N W ≤ atkinsonDyadicGapBudget N W := by
  unfold atkinsonDyadicGramBudget atkinsonDyadicGapBudget
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (sq_nonneg _) (atkinsonBlockCoefficientEnergy_nonneg _ _))
  apply Finset.sum_le_sum
  intro t ht
  apply Finset.sum_le_sum
  intro u hu
  grind

end MathCollab.Density.Stronger.Atkinson
