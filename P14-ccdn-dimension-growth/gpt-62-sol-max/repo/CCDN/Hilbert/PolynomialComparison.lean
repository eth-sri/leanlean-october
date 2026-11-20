/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Taylor

/-! Eventual inequalities compare the degree and leading coefficient of
Hilbert polynomials. -/

@[expose] public section
namespace CCDN
noncomputable section
open Filter

/-- A rational polynomial that is eventually nonnegative on the natural numbers has nonnegative
leading coefficient. -/
lemma leadingCoeff_nonneg_of_eventual_nat_eval_nonneg (P : Polynomial ℚ)
    (hP : ∃ N : ℕ, ∀ n ≥ N, 0 ≤ P.eval (n : ℚ)) : 0 ≤ P.leadingCoeff := by
  obtain ⟨N, hN⟩ := hP
  by_cases hd : P.natDegree = 0
  · have he := Polynomial.eq_C_of_natDegree_eq_zero hd
    rw [he, Polynomial.leadingCoeff_C]
    have hh := hN N le_rfl
    rw [he, Polynomial.eval_C] at hh
    exact hh
  · by_contra! hn
    have hdeg := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)
    have ht :=
      (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hn.le).comp
        tendsto_natCast_atTop_atTop
    obtain ⟨n, hnN, hneg⟩ := ((eventually_ge_atTop N).and
      (ht.eventually_lt_atBot (0 : ℚ))).exists
    exact (not_lt_of_ge (hN n hnN)) hneg

private lemma leadingCoeff_sub_nonneg {P Q : Polynomial ℚ}
    (hle : ∃ N : ℕ, ∀ n ≥ N, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    0 ≤ (Q - P).leadingCoeff := by
  obtain ⟨N, hN⟩ := hle
  exact leadingCoeff_nonneg_of_eventual_nat_eval_nonneg _
    ⟨N, fun n hn => by simpa only [Polynomial.eval_sub, sub_nonneg] using hN n hn⟩

/-- If `P` has positive leading coefficient and `P(n) ≤ Q(n)` for all large `n`, then `deg P ≤ deg
Q`. -/
lemma polynomial_natDegree_le_of_eventual_nat_eval_le
    (P Q : Polynomial ℚ) (hP : 0 < P.leadingCoeff)
    (hle : ∃ N : ℕ, ∀ n ≥ N, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.natDegree ≤ Q.natDegree := by
  have hnon := leadingCoeff_sub_nonneg hle
  by_contra! hd
  rw [Polynomial.leadingCoeff_sub_of_degree_lt' (Polynomial.degree_lt_degree hd)] at hnon
  linarith

/-- If `P` and `Q` have the same degree and positive leading coefficients and `P(n) ≤ Q(n)` for all
large `n`, then the leading coefficient of `P` is at most that of `Q`. -/
lemma polynomial_leadingCoeff_le_of_eventual_nat_eval_le
    (P Q : Polynomial ℚ) (hP : 0 < P.leadingCoeff) (hQ : 0 < Q.leadingCoeff)
    (hd : P.natDegree = Q.natDegree)
    (hle : ∃ N : ℕ, ∀ n ≥ N, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.leadingCoeff ≤ Q.leadingCoeff := by
  have hnon := leadingCoeff_sub_nonneg hle
  by_contra! hc
  have hdeg : Q.degree = P.degree := by
    rw [Polynomial.degree_eq_natDegree (Polynomial.leadingCoeff_ne_zero.mp (ne_of_gt hQ)),
      Polynomial.degree_eq_natDegree (Polynomial.leadingCoeff_ne_zero.mp (ne_of_gt hP)), hd]
  rw [Polynomial.leadingCoeff_sub_of_degree_eq hdeg (ne_of_lt hc)] at hnon
  linarith

/-- The filtered Hilbert polynomial of a proper ideal has positive leading coefficient. -/
lemma filteredHilbertPolynomial_leadingCoeff_pos {K σ : Type*} [Field K]
    [Fintype σ] [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤) :
    0 < (filteredHilbertPolynomial I).leadingCoeff := by
  obtain ⟨d, hd, _, he⟩ := filteredHilbertPolynomial_positive_multiplicity I hI
  rw [he]
  positivity

section

variable {K L σ τ : Type*} [Field K] [Field L] [Fintype σ] [Fintype τ]
  [LinearOrder σ] [LinearOrder τ]
  (I : Ideal (MvPolynomial σ K)) (J : Ideal (MvPolynomial τ L)) (hI : I ≠ ⊤)
include K L σ τ I J hI

/-- Multiplying either filtered function by a positive constant and shifting its argument
compares the degrees and (when they agree) the scaled leading coefficients. -/
theorem filteredHilbertPolynomial_compare (hJ : J ≠ ⊤) {r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (D : ℕ)
    (hle : ∀ N, r * Module.finrank K (filteredCoordinateSpace I N) ≤
      s * Module.finrank L (filteredCoordinateSpace J (N + D))) :
    let P := filteredHilbertPolynomial I
    let Q := filteredHilbertPolynomial J
    P.natDegree ≤ Q.natDegree ∧
      (P.natDegree = Q.natDegree → (r : ℚ) * P.leadingCoeff ≤ (s : ℚ) * Q.leadingCoeff) := by
  let P := Polynomial.C (r : ℚ) * filteredHilbertPolynomial I
  let Q := Polynomial.C (s : ℚ) * Polynomial.taylor (D : ℚ) (filteredHilbertPolynomial J)
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  have hs' : (0 : ℚ) < s := by exact_mod_cast hs
  have hp : 0 < P.leadingCoeff := by
    simpa only [P, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C] using mul_pos hr' (filteredHilbertPolynomial_leadingCoeff_pos I hI)
  have hq : 0 < Q.leadingCoeff := by
    simpa only [Q, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_taylor] using mul_pos hs' (filteredHilbertPolynomial_leadingCoeff_pos J hJ)
  have h : ∃ M : ℕ, ∀ N ≥ M, P.eval (N : ℚ) ≤ Q.eval (N : ℚ) := by
    obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec I
    obtain ⟨N, hN⟩ := filteredHilbertPolynomial_spec J
    refine ⟨max M N, fun n hn => ?_⟩
    simp only [P, Q, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.taylor_eval]
    rw [hM _ (by omega), ← Nat.cast_add, hN _ (by omega)]
    exact_mod_cast hle n
  change _ ≤ _ ∧ (_ = _ → _)
  refine ⟨?_, fun hd => ?_⟩
  · simpa only [P, Q, Polynomial.natDegree_C_mul hr'.ne', Polynomial.natDegree_C_mul hs'.ne', Polynomial.natDegree_taylor] using
      polynomial_natDegree_le_of_eventual_nat_eval_le P Q hp h
  · have hd' : P.natDegree = Q.natDegree := by
      simpa only [P, Q, Polynomial.natDegree_C_mul hr'.ne', Polynomial.natDegree_C_mul hs'.ne', Polynomial.natDegree_taylor] using hd
    simpa only [P, Q, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_taylor] using
      polynomial_leadingCoeff_le_of_eventual_nat_eval_le P Q hp hq hd' h

/-- Any filtered-dimension inequality between proper polynomial quotients
compares their Hilbert dimensions. -/
theorem filteredHilbertPolynomial_natDegree_le (hJ : J ≠ ⊤)
    (hle : ∀ N, Module.finrank K (filteredCoordinateSpace I N) ≤
      Module.finrank L (filteredCoordinateSpace J N)) :
    (filteredHilbertPolynomial I).natDegree ≤ (filteredHilbertPolynomial J).natDegree :=
  (filteredHilbertPolynomial_compare I J hI hJ one_pos one_pos 0 (by simpa)).1

/-- When dimensions agree, filtered comparison also compares the
leading coefficients, and hence the geometric multiplicities. -/
theorem filteredHilbertPolynomial_leadingCoeff_le (hJ : J ≠ ⊤)
    (hd : (filteredHilbertPolynomial I).natDegree = (filteredHilbertPolynomial J).natDegree)
    (hle : ∀ N, Module.finrank K (filteredCoordinateSpace I N) ≤
      Module.finrank L (filteredCoordinateSpace J N)) :
    (filteredHilbertPolynomial I).leadingCoeff ≤ (filteredHilbertPolynomial J).leadingCoeff := by
  simpa using (filteredHilbertPolynomial_compare I J hI hJ one_pos one_pos 0 (by simpa)).2 hd

end

end
end CCDN
