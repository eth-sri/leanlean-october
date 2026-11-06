/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.MonomialRays
import CCDN.ForMathlib.MvPolynomial
import CCDN.Hilbert.PlaneHilbert
import CCDN.Hilbert.StandardMonomials

/-! Finite standard-monomial prefixes for a principal equation, their exact
Hilbert ranks, and the sum of their total degrees. -/

namespace CCDN
noncomputable section
open MvPolynomial Finset

section
variable {K σ : Type*} [Field K] [Fintype σ] (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ) (N : ℕ)

/-- The finite set of standard exponents of `I`, for the monomial order `m`, of total degree at most
`N`. -/
def standardMonomialPrefix
    :
    Finset (σ →₀ ℕ) := (Set.toFinite (Ideal.boundedStandardExponents I m N)).toFinset

/-- An exponent lies in `standardMonomialPrefix I m N` exactly when it is a standard exponent of `I`
of degree at most `N`. -/
@[simp] lemma mem_standardMonomialPrefix
    (a : σ →₀ ℕ) :
    a ∈ standardMonomialPrefix I m N ↔
      a ∈ Ideal.standardExponents I m ∧ Finsupp.degree a ≤ N := by
  simp [standardMonomialPrefix, Set.Finite.mem_toFinset]
  rfl

end

section
variable {K σ : Type*} [Field K] [Fintype σ]

/-- The number of degree-lexicographic standard exponents of `I` of degree at most `N` equals the
affine Hilbert function of `I` at `N`. -/
theorem standardMonomialPrefix_card
    [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) (N : ℕ) :
    (standardMonomialPrefix I MonomialOrder.degLex N).card =
      Module.finrank K (filteredCoordinateSpace I N) := by
  rw [filteredCoordinateSpace_finrank_eq_standard_card]
  exact (Set.ncard_eq_toFinset_card _).symm

theorem standardMonomialPrefix_filter
    (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ) {N k : ℕ} (hk : k ≤ N) :
    (standardMonomialPrefix I m N).filter (fun a => Finsupp.degree a ≤ k) =
      standardMonomialPrefix I m k := by
  ext a
  simp only [mem_filter, mem_standardMonomialPrefix]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hk⟩, h.2⟩⟩

end

/-- Summation by parts for a finite set of nonnegative weights. -/
theorem sum_weights_add_prefix_counts {α : Type*} (S : Finset α) (w : α → ℕ)
    (N : ℕ) (hN : ∀ a ∈ S, w a ≤ N) :
    (∑ a ∈ S, w a) + ∑ k ∈ range N, (S.filter (fun a => w a ≤ k)).card =
      N * S.card := by
  have hcount : ∑ k ∈ range N, (S.filter (fun a => w a ≤ k)).card =
      ∑ a ∈ S, (N - w a) := by
    simp only [card_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    have he : (range N).filter (fun k => w a ≤ k) = Ico (w a) N := by grind
    rw [← card_filter, he, Nat.card_Ico]
  rw [hcount, ← sum_add_distrib]
  have he :=
    sum_congr rfl (fun a ha => Nat.add_sub_of_le (hN a ha))
  rw [he]
  simp [Nat.mul_comm]

/-- The exact principal Hilbert rank is the same binomial difference used
for homogeneous hypersurfaces with one extra variable. -/
theorem principal_standard_prefix_rank {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f ≠ 0) {N : ℕ}
    (hN : f.totalDegree ≤ N) :
    (standardMonomialPrefix (Ideal.span {f}) MonomialOrder.degLex N).card +
      (n + 1 + (N - f.totalDegree)).choose (N - f.totalDegree) =
        (n + 1 + N).choose N := by
  rw [standardMonomialPrefix_card]
  simpa [finrank_restrictTotalDegree, Fintype.card_fin] using
    principal_filtered_finrank f hf hN

