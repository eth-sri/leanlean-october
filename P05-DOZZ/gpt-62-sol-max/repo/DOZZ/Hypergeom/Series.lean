/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Defs
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Local value and derivative data of the ordinary hypergeometric series. -/

@[expose] public section

open Filter Topology

namespace DOZZ.Proofs

section
variable (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
include hc

/-- The ordinary Gauss power series converges throughout the open unit disk whenever its
denominator parameter is not a nonpositive integer. Terminating numerator parameters have
infinite radius; otherwise the radius is exactly one. -/
theorem ordinaryHypergeometricSeries_one_le_radius :
    1 ≤ (ordinaryHypergeometricSeries ℂ a b c).radius := by
  by_cases ha : ∃ n : ℕ, a = -(n : ℂ)
  · obtain ⟨n, rfl⟩ := ha
    rw [ordinaryHypergeometric_radius_top_of_neg_nat₁]
    exact le_top
  by_cases hb : ∃ n : ℕ, b = -(n : ℂ)
  · obtain ⟨n, rfl⟩ := hb
    rw [ordinaryHypergeometricSeries_symm, ordinaryHypergeometric_radius_top_of_neg_nat₁]
    exact le_top
  rw [ordinaryHypergeometricSeries_radius_eq_one ℂ a b c (by grind)]

/-- The ordinary Gauss series has positive convergence radius whenever its denominator parameter
is not a nonpositive integer. -/
theorem ordinaryHypergeometricSeries_radius_pos :
    0 < (ordinaryHypergeometricSeries ℂ a b c).radius :=
  zero_lt_one.trans_le (ordinaryHypergeometricSeries_one_le_radius a b c hc)

end

end DOZZ.Proofs
