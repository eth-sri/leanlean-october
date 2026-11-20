/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.StandardMonomials
import CCDN.ForMathlib.MvPolynomial
import CCDN.Hilbert.PlaneHilbert
public import CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile

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
    Finset (σ →₀ ℕ) := ((Finsupp.finite_of_degree_le (σ := σ) N).subset
      (t := Ideal.boundedStandardExponents I m N) fun _ ha => ha.2).toFinset

section

variable {K σ : Type*} [Field K] [Fintype σ]
include K σ

/-- An exponent lies in `standardMonomialPrefix I m N` exactly when it is a standard exponent of `I`
of degree at most `N`. -/
@[simp] lemma mem_standardMonomialPrefix
    (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ) (N : ℕ) (a : σ →₀ ℕ) :
    a ∈ standardMonomialPrefix I m N ↔
      a ∈ Ideal.standardExponents I m ∧ Finsupp.degree a ≤ N := by
  simp only [standardMonomialPrefix, Set.Finite.mem_toFinset]
  rfl

/-- The number of degree-lexicographic standard exponents of `I` of degree at most `N` equals the
affine Hilbert function of `I` at `N`. -/
theorem standardMonomialPrefix_card
    [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) (N : ℕ) :
    (standardMonomialPrefix I MonomialOrder.degLex N).card =
      Module.finrank K (filteredCoordinateSpace I N) := by
  rw [filteredCoordinateSpace_finrank_eq_standard_card]
  exact (Set.ncard_eq_toFinset_card _ ((Finsupp.finite_of_degree_le N).subset fun _ ha => ha.2)).symm

private theorem standardMonomialPrefix_filter
    (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ) {N k : ℕ} (hk : k ≤ N) :
    (standardMonomialPrefix I m N).filter (fun a => Finsupp.degree a ≤ k) =
      standardMonomialPrefix I m k := by
  grind [mem_standardMonomialPrefix]

end

/-- Summation by parts for a finite set of nonnegative weights. -/
private theorem sum_weights_add_prefix_counts {α : Type*} (S : Finset α) (w : α → ℕ)
    (N : ℕ) (hN : ∀ a ∈ S, w a ≤ N) :
    (∑ a ∈ S, w a) + ∑ k ∈ range N, (S.filter (fun a => w a ≤ k)).card =
      N * S.card := by
  classical
  have hcount : ∑ k ∈ range N, (S.filter (fun a => w a ≤ k)).card =
      ∑ a ∈ S, (N - w a) := by
    simp only [card_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    have he : (range N).filter (fun k => w a ≤ k) = Ico (w a) N := by
      aesop
    simp_all
  rw [hcount, ← sum_add_distrib]
  simp_all [Nat.mul_comm]

/-- The total degree of a standard prefix is exactly the rank-weighted
cutoff minus the preceding filtered Hilbert ranks. -/
theorem standardMonomialPrefix_weight_identity {K σ : Type*} [Field K] [Fintype σ]
    [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) (N : ℕ) :
    (∑ a ∈ standardMonomialPrefix I MonomialOrder.degLex N, Finsupp.degree a) +
        ∑ k ∈ range N, Module.finrank K (filteredCoordinateSpace I k) =
      N * Module.finrank K (filteredCoordinateSpace I N) := by
  have h := sum_weights_add_prefix_counts
    (standardMonomialPrefix I MonomialOrder.degLex N) Finsupp.degree N
    (fun a ha => (mem_standardMonomialPrefix I _ N a).mp ha |>.2)
  rw [standardMonomialPrefix_card] at h
  convert h using 2
  apply sum_congr rfl
  intro k hk
  rw [standardMonomialPrefix_filter I _ (by grind),
    standardMonomialPrefix_card]

/-- The exact principal Hilbert rank is the same binomial difference used
for homogeneous hypersurfaces with one extra variable. -/
theorem principal_standard_prefix_rank {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f ≠ 0) {N : ℕ}
    (hN : f.totalDegree ≤ N) :
    (standardMonomialPrefix (Ideal.span {f}) MonomialOrder.degLex N).card =
      hypersurfaceRank (n + 1) f.totalDegree N := by
  rw [standardMonomialPrefix_card]
  apply Nat.eq_sub_of_add_eq
  simpa only [finrank_restrictTotalDegree, Fintype.card_fin] using principal_filtered_finrank f hf hN

end
end CCDN
