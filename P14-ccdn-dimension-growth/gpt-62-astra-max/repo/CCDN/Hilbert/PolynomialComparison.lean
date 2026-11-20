/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
import Mathlib.Analysis.Polynomial.Basic

/-! Eventual inequalities compare the degree and leading coefficient of
Hilbert polynomials. -/

@[expose] public section
namespace CCDN
noncomputable section
open Filter

variable {K L σ τ : Type*} [Field K] [Field L] [Fintype σ] [Fintype τ] [LinearOrder σ]
    [LinearOrder τ] (I : Ideal (MvPolynomial σ K)) (J : Ideal (MvPolynomial τ L)) (hI : I ≠ ⊤)
    (P Q : Polynomial ℚ) (hP : 0 < P.leadingCoeff)

/-- A rational polynomial that is eventually nonnegative on the natural numbers has nonnegative
leading coefficient. -/
lemma leadingCoeff_nonneg_of_eventual_nat_eval_nonneg
    (hP : ∃ N : ℕ, ∀ n ≥ N, 0 ≤ P.eval (n : ℚ)) : 0 ≤ P.leadingCoeff := by
  obtain ⟨N, hN⟩ := hP
  by_cases hd : P.natDegree = 0
  · have he := Polynomial.eq_C_of_natDegree_eq_zero hd
    rw [he, Polynomial.leadingCoeff_C]
    have hh := hN N le_rfl
    grind [Polynomial.eval_C]
  · by_contra! hn
    have ht :=
      (P.tendsto_atBot_of_leadingCoeff_nonpos (Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)) hn.le).comp
        tendsto_natCast_atTop_atTop
    obtain ⟨n, hnN, hneg⟩ := ((eventually_ge_atTop N).and
      (ht.eventually_lt_atBot 0)).exists
    grind

include hP in
/-- If `P` has positive leading coefficient and `P(n) ≤ Q(n)` for all large `n`, then `deg P ≤ deg
Q`. -/
lemma polynomial_natDegree_le_of_eventual_nat_eval_le
    (hle : ∃ N : ℕ, ∀ n ≥ N, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.natDegree ≤ Q.natDegree := by
  have hnon : 0 ≤ (Q - P).leadingCoeff := by
    apply leadingCoeff_nonneg_of_eventual_nat_eval_nonneg
    simpa
  grind [Polynomial.leadingCoeff_sub_of_degree_lt', Polynomial.degree_lt_degree]

include hP in
/-- If `P` and `Q` have the same degree and positive leading coefficients and `P(n) ≤ Q(n)` for all
large `n`, then the leading coefficient of `P` is at most that of `Q`. -/
lemma polynomial_leadingCoeff_le_of_eventual_nat_eval_le (hQ : 0 < Q.leadingCoeff)
    (hd : P.natDegree = Q.natDegree)
    (hle : ∃ N : ℕ, ∀ n ≥ N, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.leadingCoeff ≤ Q.leadingCoeff := by
  have hnon : 0 ≤ (Q - P).leadingCoeff := by
    apply leadingCoeff_nonneg_of_eventual_nat_eval_nonneg
    simpa
  by_contra! hc
  have hdeg : Q.degree = P.degree := by
    grind [Polynomial.degree_eq_natDegree, Polynomial.leadingCoeff_ne_zero.mp, ne_of_gt]
  grind [Polynomial.leadingCoeff_sub_of_degree_eq, ne_of_lt]

include hI in
/-- The filtered Hilbert polynomial of a proper ideal has positive leading coefficient. -/
lemma filteredHilbertPolynomial_leadingCoeff_pos :
    0 < (filteredHilbertPolynomial I).leadingCoeff := by
  obtain ⟨d, hd, _, he⟩ := filteredHilbertPolynomial_positive_multiplicity I hI
  rw [he]
  positivity

include hI in
/-- Any filtered-dimension inequality between proper polynomial quotients
compares their Hilbert dimensions. -/
theorem filteredHilbertPolynomial_natDegree_le
    (hle : ∀ N, Module.finrank K (filteredCoordinateSpace I N) ≤
      Module.finrank L (filteredCoordinateSpace J N)) :
    (filteredHilbertPolynomial I).natDegree ≤ (filteredHilbertPolynomial J).natDegree := by
  apply polynomial_natDegree_le_of_eventual_nat_eval_le _ _
    (filteredHilbertPolynomial_leadingCoeff_pos I hI)
  obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec I
  obtain ⟨N, hN⟩ := filteredHilbertPolynomial_spec J
  refine ⟨max M N, fun n hn => ?_⟩
  aesop

include hI in
/-- When dimensions agree, filtered comparison also compares the
leading coefficients, and hence the geometric multiplicities. -/
theorem filteredHilbertPolynomial_leadingCoeff_le (hJ : J ≠ ⊤)
    (hd : (filteredHilbertPolynomial I).natDegree = (filteredHilbertPolynomial J).natDegree)
    (hle : ∀ N, Module.finrank K (filteredCoordinateSpace I N) ≤
      Module.finrank L (filteredCoordinateSpace J N)) :
    (filteredHilbertPolynomial I).leadingCoeff ≤ (filteredHilbertPolynomial J).leadingCoeff := by
  apply polynomial_leadingCoeff_le_of_eventual_nat_eval_le _ _
    (filteredHilbertPolynomial_leadingCoeff_pos I hI)
    (filteredHilbertPolynomial_leadingCoeff_pos J hJ) hd
  obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec I
  obtain ⟨N, hN⟩ := filteredHilbertPolynomial_spec J
  refine ⟨max M N, fun n hn => ?_⟩
  aesop

end
end CCDN
