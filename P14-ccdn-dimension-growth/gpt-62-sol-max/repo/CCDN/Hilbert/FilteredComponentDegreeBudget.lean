/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredPrimeDecomposition
import CCDN.Algebra.BinomialSectionBound
import CCDN.Hilbert.FilteredComponentRank

/-! Additivity of the leading filtered dimension bounds the total degree of
the minimal-prime components of a two-equation section. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A common linear upper bound bounds the sum of eventual slopes of incomparable primes. -/
private theorem prime_components_slope_sum_le {K σ ι : Type*} [Field K] [Finite σ] [Fintype ι]
    (I : Ideal (MvPolynomial σ K)) (P : ι → Ideal (MvPolynomial σ K))
    (hprime : ∀ i, (P i).IsPrime) (hIP : ∀ i, I ≤ P i)
    (hanti : ∀ i j, P i ≤ P j → i = j) (C T : ℕ)
    (hupper : ∀ N ≥ T, Module.finrank K (filteredCoordinateSpace I N) ≤ C * (N + 1))
    (d : ι → ℕ) (hdegree : ∀ i, HasFilteredCurveDegree (P i) (d i)) :
    ∑ i, d i ≤ C := by
  classical
  obtain ⟨D, hD⟩ := prime_components_filtered_rank_lower I P hprime hIP hanti
  choose Nᵢ cᵢ hNᵢ using hdegree
  apply eventual_linear_slope_le (fun N => ∑ i, Module.finrank K (filteredCoordinateSpace (P i) N))
    (fun N => C * (D + N + 1)) _ _ ?_ ⟨0, (C : ℤ) * (D + 1), fun N _ => by push_cast; ring⟩ T
    (fun N hN => (hD N).trans (hupper _ (by omega)))
  refine ⟨Finset.univ.sup Nᵢ, ∑ i, cᵢ i, fun N hN => ?_⟩
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hNᵢ i N ((Finset.le_sup (Finset.mem_univ i)).trans hN)

/-- Incomparable prime curves in a proper section have total degree at most the product
of the degrees of its two equations. -/
theorem polynomialSection_prime_curveDegree_sum_le {K ι : Type*} [Field K] [Fintype ι]
    (f g : MvPolynomial (Fin 3) K) (hf : Prime f) (hfg : ¬ f ∣ g)
    (P : ι → Ideal (MvPolynomial (Fin 3) K)) (hprime : ∀ i, (P i).IsPrime)
    (hIP : ∀ i, polynomialSectionIdeal f g ≤ P i)
    (hanti : ∀ i j, P i ≤ P j → i = j)
    (d : ι → ℕ) (hdegree : ∀ i, HasFilteredCurveDegree (P i) (d i)) :
    ∑ i, d i ≤ f.totalDegree * g.totalDegree := by
  apply prime_components_slope_sum_le _ P hprime hIP hanti _ (f.totalDegree + g.totalDegree) _ d hdegree
  intro N hN
  have hh := filteredCoordinateSpace_codim_two_bound (n := 1) hf hfg
    (polynomialSectionIdeal f g) (polynomialSectionIdeal_first_mem f g)
    (polynomialSectionIdeal_second_mem f g) hN
  simpa [Nat.choose_one_right, Nat.add_comm 1] using hh

end
end CCDN
