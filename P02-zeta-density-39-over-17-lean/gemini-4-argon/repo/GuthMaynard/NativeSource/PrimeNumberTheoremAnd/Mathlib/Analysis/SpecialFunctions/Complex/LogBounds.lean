/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Logarithm estimates for Weierstrass products

This file develops the finite truncation and tail estimates for the logarithm series
`-log (1 - z)`.  These estimates are the local analytic input for bounding Weierstrass
factors and canonical products.
-/

public section

open scoped BigOperators


namespace Complex

open scoped BigOperators in
/-- On the open unit disk, `-log (1 - z)` is the `tsum` with index shift `n ↦ n + 1`. -/
lemma neg_log_one_sub_eq_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    -log (1 - z) = ∑' n : ℕ, z ^ (n + 1) / (n + 1) := by
  have h := hasSum_taylorSeries_neg_log hz
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  simp only [pow_zero, Nat.cast_zero, div_zero, zero_add, Nat.cast_add, Nat.cast_one]














