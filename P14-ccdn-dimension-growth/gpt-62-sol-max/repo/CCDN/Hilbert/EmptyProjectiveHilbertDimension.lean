/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveSection
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Height.ProjectiveBox
import CCDN.Hilbert.FilteredHilbertLinearity

/-! A projective point supplies a transcendental coordinate along its affine line. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A projective zero gives at least linear growth of the filtered Hilbert function. -/
theorem hilbert_dimension_pos_of_projective_zero {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) {x : ProjectivePoint n}
    (hx : x ∈ projectiveIdealZeroLocus I) : 0 < (filteredHilbertPolynomial I).natDegree := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp x.rep_nonzero
  change x.rep j ≠ 0 at hj
  have ht : Transcendental ℚ (Ideal.Quotient.mk I (X j)) := by
    apply transcendental_iff.mpr
    intro p hp
    have hmem : Polynomial.aeval (X j) p ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ ℚ I) (X j) p).symm.trans hp
    suffices Polynomial.X * p = 0 by simpa using this
    apply Polynomial.funext
    intro a
    by_cases ha : a = 0
    · simp [ha]
    let c := a / x.rep j
    have hv := smul_ne_zero (div_ne_zero ha hj) x.rep_nonzero
    have he : Projectivization.mk ℚ (c • x.rep) hv = x := by
      conv_rhs => rw [← x.mk_rep]
      exact (Projectivization.mk_eq_mk_iff' ..).mpr ⟨c, rfl⟩
    have h := hx _ hv he _ hmem
    change aeval (c • x.rep) (Polynomial.aeval (X j) p) = 0 at h
    rw [← Polynomial.aeval_algHom_apply (aeval (c • x.rep)), aeval_X, Pi.smul_apply,
      smul_eq_mul, div_mul_cancel₀ _ hj, Polynomial.coe_aeval_eq_eval] at h
    simp [h]
  by_contra! h
  have hP := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero h)
  obtain ⟨N, hN⟩ := filteredHilbertPolynomial_spec I
  let M := N + Module.finrank ℚ (filteredCoordinateSpace I N)
  have he := hN M (by omega)
  have he' := hN N le_rfl
  rw [hP, Polynomial.eval_C] at he he'
  have heq : Module.finrank ℚ (filteredCoordinateSpace I M) =
      Module.finrank ℚ (filteredCoordinateSpace I N) := by exact_mod_cast he.symm.trans he'
  have := transcendental_coordinate_filtered_lower I ht M
  omega

/-- A constant filtered Hilbert polynomial has empty projective zero locus. -/
theorem projectiveIdealZeroLocus_eq_empty_of_hilbert_dimension_zero
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (hdim : (filteredHilbertPolynomial I).natDegree = 0) :
    projectiveIdealZeroLocus I = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun _ hx =>
    (Nat.ne_of_gt (hilbert_dimension_pos_of_projective_zero I hx)) hdim

end
end CCDN
