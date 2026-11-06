/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.ProjectiveSection
import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Algebra.GridPointInterpolation
import CCDN.Algebra.ProjectiveFiniteFibers

/-! A coordinate ring with constant filtered Hilbert polynomial has
finitely many rational affine zeros. Its projective zero locus is empty,
since every nonzero representative would produce arbitrarily many affine
zeros by scaling. -/

namespace CCDN
section
open MvPolynomial

theorem finite_point_bound_of_hilbert_dimension_zero
    {σ : Type*} [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ ℚ)) (hdim : (filteredHilbertPolynomial I).natDegree = 0) :
    ∃ M : ℕ, ∀ s : Finset (σ → ℚ),
      (∀ x ∈ s, x ∈ idealZeroLocus I) → s.card ≤ M := by
  obtain ⟨N₀, hN₀⟩ := filteredHilbertPolynomial_spec I
  have hP := Polynomial.eq_C_of_natDegree_eq_zero hdim
  refine ⟨Module.finrank ℚ (filteredCoordinateSpace I N₀), ?_⟩
  intro s hs
  let S : Finset ℚ := s.biUnion (fun x => Finset.univ.image x)
  let N := max N₀ (Fintype.card σ * (S.card - 1))
  have hdimN : Module.finrank ℚ (filteredCoordinateSpace I N) =
      Module.finrank ℚ (filteredCoordinateSpace I N₀) := by
    have h₁ := hN₀ N (le_max_left _ _)
    have h₂ := hN₀ N₀ le_rfl
    rw [hP, Polynomial.eval_C] at h₁ h₂
    exact_mod_cast h₁.symm.trans h₂
  have hh := grid_points_filtered_lower I S (fun x : s => x.val)
    Subtype.val_injective (fun x j => by grind)
    (fun x f hf => hs x.val x.property f hf) (le_max_right _ _ : _ ≤ N)
  have hh' : s.card ≤ Module.finrank ℚ (filteredCoordinateSpace I N) := by
    simpa using hh
  exact hh'.trans_eq hdimN

