/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.MonomialRays
import CCDN.ForMathlib.MvPolynomial
import CCDN.Hilbert.PlaneHilbert
import CCDN.Hilbert.StandardMonomials

/-! Finite standard-monomial prefixes for a principal equation, their exact
Hilbert ranks, and the sum of their total degrees. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The finite set of standard exponents of `I`, for the monomial order `m`, of total degree at most
`N`. -/
def standardMonomialPrefix {K σ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ) (N : ℕ) :
    Finset (σ →₀ ℕ) := (Set.toFinite (Ideal.boundedStandardExponents I m N)).toFinset

/-- An exponent lies in `standardMonomialPrefix I m N` exactly when it is a standard exponent of `I`
of degree at most `N`. -/
@[simp] lemma mem_standardMonomialPrefix {K σ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ) (N : ℕ) (a : σ →₀ ℕ) :
    a ∈ standardMonomialPrefix I m N ↔
      a ∈ Ideal.standardExponents I m ∧ Finsupp.degree a ≤ N := by
  simp only [standardMonomialPrefix, Set.Finite.mem_toFinset]
  rfl

/-- The number of degree-lexicographic standard exponents of `I` of degree at most `N` equals the
affine Hilbert function of `I` at `N`. -/
theorem standardMonomialPrefix_card {K σ : Type*} [Field K] [Fintype σ]
    [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) (N : ℕ) :
    (standardMonomialPrefix I MonomialOrder.degLex N).card =
      Module.finrank K (filteredCoordinateSpace I N) := by
  rw [filteredCoordinateSpace_finrank_eq_standard_card]
  exact (Set.ncard_eq_toFinset_card _).symm

/-- The total degree of a standard prefix is exactly the rank-weighted
cutoff minus the preceding filtered Hilbert ranks. -/
theorem standardMonomialPrefix_weight_identity {K σ : Type*} [Field K] [Fintype σ]
    [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) (N : ℕ) :
    (∑ a ∈ standardMonomialPrefix I MonomialOrder.degLex N, Finsupp.degree a) +
        ∑ k ∈ range N, Module.finrank K (filteredCoordinateSpace I k) =
      N * Module.finrank K (filteredCoordinateSpace I N) := by
  classical
  let S := standardMonomialPrefix I MonomialOrder.degLex N
  have hfilt {k : ℕ} (hk : k ≤ N) :
      S.filter (fun a => Finsupp.degree a ≤ k) = standardMonomialPrefix I MonomialOrder.degLex k := by
    ext a
    simp only [S, mem_filter, mem_standardMonomialPrefix]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hk⟩, h.2⟩⟩
  have hcount : ∑ k ∈ range N, Module.finrank K (filteredCoordinateSpace I k) =
      ∑ a ∈ S, (N - Finsupp.degree a) := by
    have hsum : ∑ k ∈ range N, Module.finrank K (filteredCoordinateSpace I k) =
        ∑ k ∈ range N, (S.filter (fun a => Finsupp.degree a ≤ k)).card :=
      sum_congr rfl fun k hk => by
        rw [hfilt (by have := mem_range.mp hk; omega), standardMonomialPrefix_card]
    rw [hsum]
    simp only [card_filter]
    rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [← card_filter, show (range N).filter (fun k => Finsupp.degree a ≤ k) =
      Ico (Finsupp.degree a) N by ext k; simp only [mem_filter, mem_range, mem_Ico]; omega,
      Nat.card_Ico]
  rw [hcount, ← sum_add_distrib, ← standardMonomialPrefix_card]
  have he : ∑ a ∈ S, (Finsupp.degree a + (N - Finsupp.degree a)) = ∑ _a ∈ S, N :=
    sum_congr rfl fun a ha => Nat.add_sub_of_le ((mem_standardMonomialPrefix I _ N a).mp ha).2
  rw [he]; simp [S, Nat.mul_comm]

/-- The exact principal Hilbert rank is the same binomial difference used
for homogeneous hypersurfaces with one extra variable. -/
theorem principal_standard_prefix_rank {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f ≠ 0) {N : ℕ}
    (hN : f.totalDegree ≤ N) :
    (standardMonomialPrefix (Ideal.span {f}) MonomialOrder.degLex N).card +
      (n + 1 + (N - f.totalDegree)).choose (N - f.totalDegree) =
        (n + 1 + N).choose N := by
  rw [standardMonomialPrefix_card]
  simpa only [finrank_restrictTotalDegree, Fintype.card_fin] using
    principal_filtered_finrank f hf hN

end
end CCDN
