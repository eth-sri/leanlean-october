/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Algebra.ProjectiveSection
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Algebra.GridPointInterpolation
import CCDN.Algebra.ProjectiveFiniteFibers

/-! A coordinate ring with constant filtered Hilbert polynomial has
finitely many rational affine zeros. Its projective zero locus is empty,
since every nonzero representative would produce arbitrarily many affine
zeros by scaling. -/

public section
namespace CCDN
open MvPolynomial

private theorem finite_point_bound_of_hilbert_dimension_zero
    {σ : Type*} [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ ℚ)) (hdim : (filteredHilbertPolynomial I).natDegree = 0) :
    ∃ M : ℕ, ∀ s : Finset (σ → ℚ),
      (∀ x ∈ s, x ∈ idealZeroLocus I) → s.card ≤ M := by
  classical
  obtain ⟨N₀, hN₀⟩ := filteredHilbertPolynomial_spec I
  have hP := Polynomial.eq_C_of_natDegree_eq_zero hdim
  refine ⟨Module.finrank ℚ (filteredCoordinateSpace I N₀), ?_⟩
  intro s hs
  let S := s.biUnion (fun x => Finset.univ.image x)
  let N := max N₀ (Fintype.card σ * (S.card - 1))
  have hdimN := by
    have h₁ := hN₀ N (le_max_left _ _)
    have h₂ := hN₀ N₀ le_rfl
    rw [hP, Polynomial.eval_C] at h₁ h₂
    exact_mod_cast h₁.symm.trans h₂
  have hh := grid_points_filtered_lower I S ((Subtype.val))
    Subtype.val_injective (fun x j => by
      grind)
    (fun x f hf => hs x.val x.property f hf) (le_max_right _ _ : _ ≤ N)
  have hh' := by
    simpa only [Fintype.card_coe] using hh
  exact hh'.trans_eq hdimN

/-- An ideal of `ℚ[X₀, …, Xₙ]` whose filtered Hilbert polynomial is constant has empty projective
zero locus. -/
theorem projectiveIdealZeroLocus_eq_empty_of_hilbert_dimension_zero
    {n : ℕ} (I : CCDN.CoordinateIdeal (n + 1))
    (hdim : (filteredHilbertPolynomial I).natDegree = 0) :
    projectiveIdealZeroLocus I = ∅ := by
  obtain ⟨M, hM⟩ := finite_point_bound_of_hilbert_dimension_zero I hdim
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh := projective_linear_image_ne_zero_of_finite_zero_fiber I
    (0 : (CCDN.RatPoint (n + 1)) →ₗ[ℚ] (CCDN.RatPoint 0)) M
    (fun s hs _ => hM s hs) x hx
  exact hh rfl

end CCDN
