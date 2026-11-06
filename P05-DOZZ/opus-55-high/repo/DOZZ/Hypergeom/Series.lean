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
variable (a b c : ℂ)
section
variable (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
include hc

/-- The ordinary Gauss series has positive convergence radius whenever its denominator parameter
is not a nonpositive integer. -/
theorem ordinaryHypergeometricSeries_radius_pos :
    0 < (ordinaryHypergeometricSeries ℂ a b c).radius := by
  by_cases ha : ∃ n : ℕ, a = -(n : ℂ)
  · obtain ⟨n, hn⟩ := ha
    have htop : (ordinaryHypergeometricSeries ℂ a b c).radius = ⊤ := by
      rw [hn]
      exact ordinaryHypergeometric_radius_top_of_neg_nat₁ ℂ b c
    simp_all
  · by_cases hb : ∃ n : ℕ, b = -(n : ℂ)
    · obtain ⟨n, hn⟩ := hb
      have htop : (ordinaryHypergeometricSeries ℂ a b c).radius = ⊤ := by
        rw [ordinaryHypergeometricSeries_symm, hn]
        exact ordinaryHypergeometric_radius_top_of_neg_nat₁ ℂ a c
      simp_all
    · have ha' : ∀ n : ℕ, (n : ℂ) ≠ -a := by
        grind
      have hb' : ∀ n : ℕ, (n : ℂ) ≠ -b := by
        grind
      have hc' : ∀ n : ℕ, (n : ℂ) ≠ -c := by
        grind
      rw [ordinaryHypergeometricSeries_radius_eq_one ℂ a b c (fun n => ⟨ha' n, hb' n, hc' n⟩)]
      norm_num

/-- The ordinary Gauss power series converges throughout the open unit disk whenever its
denominator parameter is not a nonpositive integer. Terminating numerator parameters have
infinite radius; otherwise the radius is exactly one. -/
theorem ordinaryHypergeometricSeries_one_le_radius :
    1 ≤ (ordinaryHypergeometricSeries ℂ a b c).radius := by
  by_cases ha : ∃ n : ℕ, a = -(n : ℂ)
  · obtain ⟨n, hn⟩ := ha
    have htop : (ordinaryHypergeometricSeries ℂ a b c).radius = ⊤ := by
      rw [hn]
      exact ordinaryHypergeometric_radius_top_of_neg_nat₁ ℂ b c
    simp_all
  · by_cases hb : ∃ n : ℕ, b = -(n : ℂ)
    · obtain ⟨n, hn⟩ := hb
      have htop : (ordinaryHypergeometricSeries ℂ a b c).radius = ⊤ := by
        rw [ordinaryHypergeometricSeries_symm, hn]
        exact ordinaryHypergeometric_radius_top_of_neg_nat₁ ℂ a c
      simp_all
    · have ha' : ∀ n : ℕ, (n : ℂ) ≠ -a := by
        grind
      have hb' : ∀ n : ℕ, (n : ℂ) ≠ -b := by
        grind
      have hc' : ∀ n : ℕ, (n : ℂ) ≠ -c := by
        grind
      rw [ordinaryHypergeometricSeries_radius_eq_one ℂ a b c
        (fun n => ⟨ha' n, hb' n, hc' n⟩)]

end

end

end DOZZ.Proofs
