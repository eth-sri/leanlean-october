/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.EmptyProjectiveHilbertDimension
import CCDN.Height.ProjectivePointSeparation
import CCDN.Height.ProjectiveZeroLocus
import CCDN.Hilbert.ProperSectionHilbert

/-! A linear section cannot contain one of two distinct points on a prime of Hilbert dimension one. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A prime projective variety of dimension zero has at most one rational point. -/
theorem zero_dimensional_projective_count_le
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    (hdim : (filteredHilbertPolynomial I).natDegree = 1) (B : ℝ) :
    projectiveCount (projectiveIdealZeroLocus I) B ≤ 1 := by
  by_contra! h
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h
  have hxI := (mem_projectivePoints.mp hx).2
  have hyI := (mem_projectivePoints.mp hy).2
  obtain ⟨f, hf, hfx, hfy⟩ := exists_homogeneous_linear_separator y.rep_nonzero (x := x.rep)
    (fun c hc => hxy (by
      rw [← x.mk_rep, ← y.mk_rep, Projectivization.mk_eq_mk_iff']
      exact ⟨c, hc⟩))
  have hfI := fun h => one_ne_zero (hfx.symm.trans (projectiveIdealZeroLocus_rep hxI f h))
  let J := I ⊔ Ideal.span {f}
  have hyJ : y ∈ projectiveIdealZeroLocus J := by
    intro v hv he g hg
    have hvf := (homogeneous_eval_zero_iff_projective_eq hf hv y.rep_nonzero
      (he.trans y.mk_rep.symm)).mpr hfy
    exact (sup_le (show I ≤ RingHom.ker (eval v) from hyI v hv he)
      (Ideal.span_singleton_le_iff_mem _ |>.mpr hvf)) hg
  have hJ : J ≠ ⊤ := fun h => (show (1 : ℚ) ≠ 0 by decide) (by
    simpa using projectiveIdealZeroLocus_rep hyJ 1 (by simp [h]))
  have hle : (filteredHilbertPolynomial J).natDegree ≤ 0 :=
    proper_section_hilbert_dimension_le I 0 hdim f hfI hJ
  have hpos := hilbert_dimension_pos_of_projective_zero J hyJ
  omega

end
end CCDN
