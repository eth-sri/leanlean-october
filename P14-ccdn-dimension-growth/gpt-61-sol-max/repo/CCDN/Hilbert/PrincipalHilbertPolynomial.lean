/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Hilbert.FilteredHilbertPolynomial
public import Mathlib.RingTheory.Polynomial.HilbertPoly
import CCDN.ForMathlib.MvPolynomial
import CCDN.Hilbert.PlaneHilbert
import Mathlib.Tactic.Positivity

/-! The filtered Hilbert polynomial of a principal hypersurface.
Its dimension and multiplicity follow from the exact finite-dimensional
principal-ideal rank identity, without geometric hypotheses. -/

public section
namespace CCDN
open MvPolynomial Finset

private lemma principal_binomial_layer_sum (n d N : ℕ) (hN : d ≤ N) :
    (∑ i ∈ range d, (N + n - i).choose n) +
      (N - d + (n + 1)).choose (n + 1) = (N + (n + 1)).choose (n + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    grind [sum_range_succ]

variable {K : Type*} [Field K] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) K) (hf : f ≠ 0)

include hf in
/-- Exact filtered Hilbert polynomial of any nonzero principal equation
in n+1 variables, including the constant case. -/
private theorem principal_filteredHilbertPolynomial  :
    filteredHilbertPolynomial (Ideal.span {f}) =
      ∑ i ∈ range f.totalDegree, Polynomial.preHilbertPoly ℚ n i := by
  apply filteredHilbertPolynomial_eq_of_eventual
  refine ⟨f.totalDegree, fun N hN => ?_⟩
  have hr := principal_filtered_finrank f hf hN
  rw [finrank_restrictTotalDegree, finrank_restrictTotalDegree] at hr
  simp only [Fintype.card_fin] at hr
  rw [← Nat.choose_symm_add  ,
    ← Nat.choose_symm_add  ] at hr
  have hs := principal_binomial_layer_sum n f.totalDegree N hN
  have he : Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) N) =
      ∑ i ∈ range f.totalDegree, (N + n - i).choose n := by
    grind
  rw [he, Polynomial.eval_finsetSum, Nat.cast_sum]
  apply sum_congr rfl
  intro i hi
  exact Polynomial.preHilbertPoly_eq_choose_add_sub ℚ n (by have := mem_range.mp hi; omega)


include hf in
/-- A nonconstant principal equation in n+1 variables has filtered
Hilbert dimension n and multiplicity equal to its total degree. -/
theorem principal_filteredHilbertPolynomial_degree_leadingCoeff
     (hd : 0 < f.totalDegree) :
    HasAffineDimensionDegree (Ideal.span {f}) n f.totalDegree := by
  have hP := principal_filteredHilbertPolynomial f hf
  have hcoeff := (show (∑ i ∈ range f.totalDegree, Polynomial.preHilbertPoly ℚ n i).coeff n = ↑f.totalDegree / ↑n.factorial from (by
                   simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_preHilbertPoly_self,
                     sum_const, card_range, nsmul_eq_mul, div_eq_mul_inv]))
  have hn : (∑ i ∈ range f.totalDegree, Polynomial.preHilbertPoly ℚ n i).coeff n ≠ 0 := by
    rw [hcoeff]
    positivity
  have hdegree := le_antisymm ((by
                                 simp_all [Polynomial.natDegree_sum_le_of_forall_le, Polynomial.natDegree_preHilbertPoly]))
    (Polynomial.le_natDegree_of_ne_zero hn)
  exact ⟨by rw [hP, hdegree], by rw [hP, Polynomial.leadingCoeff, hdegree, hcoeff]⟩

include hf in
/-- The filtered Hilbert polynomial of a nonconstant principal ideal `(f)` in `n + 1` variables has
degree `n`. -/
theorem principal_filteredHilbertPolynomial_natDegree
     (hd : 0 < f.totalDegree) :
    (filteredHilbertPolynomial (Ideal.span {f})).natDegree = n :=
  (principal_filteredHilbertPolynomial_degree_leadingCoeff f hf hd).natDegree_eq

include hf in
/-- The filtered Hilbert polynomial of a nonconstant principal ideal `(f)` in `n + 1` variables has
leading coefficient `deg f / n!`, so the hypersurface has degree `deg f`. -/
theorem principal_filteredHilbertPolynomial_leadingCoeff
     (hd : 0 < f.totalDegree) :
    (filteredHilbertPolynomial (Ideal.span {f})).leadingCoeff =
      ↑f.totalDegree / n.factorial :=
  (principal_filteredHilbertPolynomial_degree_leadingCoeff f hf hd).leadingCoeff_eq

end CCDN
