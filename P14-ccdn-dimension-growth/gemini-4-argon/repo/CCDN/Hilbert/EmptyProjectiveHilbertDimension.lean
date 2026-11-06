/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveSection
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Algebra.GridPointInterpolation
import CCDN.Algebra.ProjectiveFiniteFibers

/-! A coordinate ring with constant filtered Hilbert polynomial has
finitely many rational affine zeros. Its projective zero locus is empty,
since every nonzero representative would produce arbitrarily many affine
zeros by scaling. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- An ideal of `ℚ[X₀, …, Xₙ]` whose filtered Hilbert polynomial is constant has empty projective
zero locus. -/
theorem projectiveIdealZeroLocus_eq_empty_of_hilbert_dimension_zero
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (hdim : (filteredHilbertPolynomial I).natDegree = 0) :
    projectiveIdealZeroLocus I = ∅ := by
  classical
  obtain ⟨N₀, hN₀⟩ := filteredHilbertPolynomial_spec I
  have hP := Polynomial.eq_C_of_natDegree_eq_zero hdim
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
    projective_linear_image_ne_zero_of_finite_zero_fiber I
      (0 : (Fin (n + 1) → ℚ) →ₗ[ℚ] (Fin 0 → ℚ))
      (Module.finrank ℚ (filteredCoordinateSpace I N₀)) (fun s hs _ => ?_) x hx rfl
  let S : Finset ℚ := s.biUnion (fun x => Finset.univ.image x)
  let N := max N₀ ((n + 1) * (S.card - 1))
  have h₁ := hN₀ N (le_max_left _ _)
  have h₂ := hN₀ N₀ le_rfl
  rw [hP, Polynomial.eval_C] at h₁ h₂
  have hh := grid_points_filtered_lower I S (fun x : s => x.val)
    Subtype.val_injective
    (fun x j => Finset.mem_biUnion.mpr ⟨x.val, x.property, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩)
    (fun x f hf => hs x.val x.property f hf) (N := N) (by simp [N])
  exact (by simpa only [Fintype.card_coe] using hh :
    s.card ≤ Module.finrank ℚ (filteredCoordinateSpace I N)).trans_eq (mod_cast h₁.symm.trans h₂)

end
end CCDN
