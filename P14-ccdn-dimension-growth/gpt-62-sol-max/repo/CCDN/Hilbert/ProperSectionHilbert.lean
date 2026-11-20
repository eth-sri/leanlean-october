/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Hilbert.PolynomialComparison
import Mathlib.Algebra.Polynomial.Taylor

/-! Hilbert inequalities for a proper polynomial section of a prime
affine variety. Multiplication by the section is injective in the original
coordinate domain and is killed in the section quotient. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem proper_section_filtered_hilbert_drop
    {K σ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (f : MvPolynomial σ K) (hf : f ∉ I) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace (I ⊔ Ideal.span {f}) (f.totalDegree + N)) +
      Module.finrank K (filteredCoordinateSpace I N) ≤
        Module.finrank K (filteredCoordinateSpace I (f.totalDegree + N)) := by
  rw [← filteredCoordinateSpace_map_quotient I _ le_sup_left]
  exact filtered_section_image_finrank_add_le I _ hf le_rfl
    (Ideal.Quotient.eq_zero_iff_mem.mpr ((show Ideal.span {f} ≤ I ⊔ Ideal.span {f} from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton f)))) N

section

variable {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
  (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
include K σ I

open Polynomial in
private theorem proper_section_hilbert_polynomial_difference
    (f : MvPolynomial σ K) (hf : f ∉ I) :
    ∃ M : ℕ, ∀ N ≥ M,
      (taylor (f.totalDegree : ℚ) (filteredHilbertPolynomial (I ⊔ Ideal.span {f}))).eval (N : ℚ) ≤
      (taylor (f.totalDegree : ℚ) (filteredHilbertPolynomial I) -
        filteredHilbertPolynomial I).eval (N : ℚ) := by
  obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec I
  obtain ⟨L, hL⟩ := filteredHilbertPolynomial_spec (I ⊔ Ideal.span {f})
  refine ⟨max M L, fun N hN => ?_⟩
  rw [Polynomial.eval_sub, taylor_eval, taylor_eval, add_comm (N : ℚ), ← Nat.cast_add,
    hM _ (by omega), hM N (by omega), hL _ (by omega), le_sub_iff_add_le]
  exact_mod_cast proper_section_filtered_hilbert_drop I f hf N

open Polynomial in
/-- Cutting a prime ideal by a polynomial outside it lowers the Hilbert dimension. -/
theorem proper_section_hilbert_dimension_le
    (m : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (f : MvPolynomial σ K) (hf : f ∉ I)
    (hsection : I ⊔ Ideal.span {f} ≠ ⊤) :
    (filteredHilbertPolynomial (I ⊔ Ideal.span {f})).natDegree ≤ m := by
  let P := filteredHilbertPolynomial I
  let Q := taylor (f.totalDegree : ℚ) P - P
  have hP : P ≠ 0 := by intro h; simp [P, h] at hdim
  have hQ : Q.natDegree ≤ m := by
    by_cases h : Q = 0
    · simp [h]
    have hlt := degree_sub_lt_right (degree_taylor P (f.totalDegree : ℚ)) hP
      (leadingCoeff_taylor (f.totalDegree : ℚ) P)
    change Q.degree < P.degree at hlt
    rw [degree_eq_natDegree h, degree_eq_natDegree hP, Nat.cast_lt] at hlt
    change P.natDegree = m + 1 at hdim
    omega
  have h := polynomial_natDegree_le_of_eventual_nat_eval_le _ Q
    (by simpa only [leadingCoeff_taylor] using filteredHilbertPolynomial_leadingCoeff_pos _ hsection)
    (proper_section_hilbert_polynomial_difference I f hf)
  rw [natDegree_taylor] at h
  exact h.trans hQ

end

end
end CCDN
