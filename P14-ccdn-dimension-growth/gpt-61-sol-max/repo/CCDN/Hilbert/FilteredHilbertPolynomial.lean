/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.ForMathlib.StandardExponents
public import CCDN.Hilbert.FilteredIntersection
import CCDN.Hilbert.OrthantMultiplicity
import CCDN.Hilbert.StandardMonomials
import Mathlib.Order.Interval.Set.Infinite

/-! Existence, uniqueness and positive integral multiplicity of the
filtered Hilbert polynomial of a polynomial quotient, in arbitrary finite
dimension. These results construct the polynomial from standard exponents. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The exponent vectors, as functions `σ → ℕ`, of the standard monomials of `I` with respect to the
monomial order `m`: those that are not leading monomials of elements of `I`. -/
def standardExponentVectors {K σ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ)  :=
  {a | Finsupp.equivFunOnFinite.symm a ∈ Ideal.standardExponents I m}

/-- The standard exponent vectors of an ideal form a lower set. -/
lemma standardExponentVectors_lower {K σ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ) :
    IsLowerSet (standardExponentVectors I m) := by
  solve_by_elim [Ideal.isLowerSet_standardExponents]

variable {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ] (I : Ideal (MvPolynomial σ K))

/-- A proper ideal has a standard exponent vector for the degree-lexicographic order. -/
lemma standardExponentVectors_nonempty  (hI : I ≠ ⊤) :
    (standardExponentVectors I MonomialOrder.degLex).Nonempty := by
  obtain ⟨r, hr, _, hmem⟩ := Ideal.exists_standard_representative_degLex I 1
  have hr0 : r ≠ 0 := by
    grind [Ideal.eq_top_of_isUnit_mem]
  obtain ⟨a, ha⟩ := support_nonempty.mpr hr0
  refine ⟨Finsupp.equivFunOnFinite a, ?_⟩
  change Finsupp.equivFunOnFinite.symm (Finsupp.equivFunOnFinite a) ∈
    Ideal.standardExponents I MonomialOrder.degLex
  rw [Equiv.symm_apply_apply]
  exact hr ha

/-- The affine Hilbert function of `I` at `N` equals the number of standard exponent vectors of `I`,
for the degree-lexicographic order, of total degree at most `N`. -/
lemma filteredCoordinateSpace_finrank_eq_vector_card  (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace I N) =
      Nat.card {a : σ → ℕ //
        a ∈ standardExponentVectors I MonomialOrder.degLex ∧ ∑ i, a i ≤ N} := by
  rw [filteredCoordinateSpace_finrank_eq_standard_card]
  apply Nat.card_congr
  exact Finsupp.equivFunOnFinite.subtypeEquiv (fun a => by
    simp [Ideal.boundedStandardExponents, standardExponentVectors, Finsupp.degree_eq_sum])

/-- Eventual polynomiality of the filtered coordinate-space dimension. -/
theorem filteredCoordinateSpace_eventually_polynomial  :
    ∃ P : Polynomial ℚ, ∃ N : ℕ, ∀ n ≥ N,
      P.eval ↑n = (Module.finrank K (filteredCoordinateSpace I n) : ℚ) := by
  obtain ⟨P, N, hN⟩ := lowerSet_eventually_polynomial
    (standardExponentVectors I MonomialOrder.degLex)
    (standardExponentVectors_lower I MonomialOrder.degLex)
  refine ⟨P, N, fun n hn => ?_⟩
  rw [filteredCoordinateSpace_finrank_eq_vector_card]
  exact hN n hn

/-- Two rational polynomials that agree at all sufficiently large natural numbers are equal. -/
lemma polynomial_eq_of_eventual_nat_eval_eq (P Q : Polynomial ℚ)
    (h : ∃ N : ℕ, ∀ n ≥ N, P.eval ↑n = Q.eval ↑n) : P = Q := by
  obtain ⟨N, hN⟩ := h
  apply Polynomial.eq_of_infinite_eval_eq
  apply ((Set.Ici_infinite N).image (Nat.cast_injective ).injOn).mono
  rintro x ⟨n, hn, rfl⟩
  exact hN n hn

/-- The uniquely determined filtered Hilbert polynomial. -/
def filteredHilbertPolynomial   :=
  (filteredCoordinateSpace_eventually_polynomial I).choose

/-- The filtered Hilbert polynomial of `I` has degree `m` and leading coefficient `d / m!`:
the affine variety cut out by `I` has dimension `m` and degree `d`. -/
structure HasAffineDimensionDegree {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (m d : ℕ) : Prop where
  /-- The filtered Hilbert polynomial has degree `m`. -/
  natDegree_eq : (filteredHilbertPolynomial I).natDegree = m
  /-- The filtered Hilbert polynomial has leading coefficient `d / m!`. -/
  leadingCoeff_eq : (filteredHilbertPolynomial I).leadingCoeff = ↑d / m.factorial

/-- The cone over `I` has filtered Hilbert polynomial of degree `m + 1` and leading coefficient
`d / (m + 1)!`. For a homogeneous ideal `I` this says that the projective variety cut out by `I`
has dimension `m` and degree `d`; it is the affine dimension and degree of the cone. -/
abbrev HasProjectiveDimensionDegree  (m d : ℕ)  :=
  HasAffineDimensionDegree I (m + 1) d

/-- The filtered Hilbert polynomial of `I` agrees at every sufficiently large `n` with the dimension
of the image in `K[X] ⧸ I` of the polynomials of total degree at most `n`. -/
theorem filteredHilbertPolynomial_spec  :
    ∃ N : ℕ, ∀ n ≥ N, (filteredHilbertPolynomial I).eval ↑n =
      (Module.finrank K (filteredCoordinateSpace I n) : ℚ) :=
  (filteredCoordinateSpace_eventually_polynomial I).choose_spec

/-- Any rational polynomial that eventually agrees with the affine Hilbert function of `I` is the
filtered Hilbert polynomial of `I`. -/
theorem filteredHilbertPolynomial_eq_of_eventual  (P : Polynomial ℚ)
    (hP : ∃ N : ℕ, ∀ n ≥ N, P.eval ↑n =
      (Module.finrank K (filteredCoordinateSpace I n) : ℚ)) :
    filteredHilbertPolynomial I = P := by
  obtain ⟨N, hN⟩ := filteredHilbertPolynomial_spec I
  obtain ⟨M, hM⟩ := hP
  apply polynomial_eq_of_eventual_nat_eval_eq
  refine ⟨max N M, fun n hn => ?_⟩
  rw [hN n ((le_max_left _ _).trans hn), hM n ((le_max_right _ _).trans hn)]

/-- Proper polynomial quotients have a positive integer factorial-normalized
leading coefficient. -/
theorem filteredHilbertPolynomial_positive_multiplicity  (hI : I ≠ ⊤) :
    ∃ d : ℕ, 0 < d ∧
      (filteredHilbertPolynomial I).natDegree ≤ Fintype.card σ ∧
      (filteredHilbertPolynomial I).leadingCoeff =
        ↑d / (filteredHilbertPolynomial I).natDegree.factorial := by
  obtain ⟨P, d, hd, hdeg, hlc, N, hN⟩ := lowerSet_eventually_polynomial_positive
    (standardExponentVectors I MonomialOrder.degLex)
    (standardExponentVectors_lower I MonomialOrder.degLex)
    (standardExponentVectors_nonempty I hI)
  have he : filteredHilbertPolynomial I = P := by
    apply filteredHilbertPolynomial_eq_of_eventual
    refine ⟨N, fun n hn => ?_⟩
    rw [filteredCoordinateSpace_finrank_eq_vector_card]
    exact hN n hn
  exact ⟨d, hd, he.symm ▸ hdeg, he.symm ▸ hlc⟩

end
end CCDN
