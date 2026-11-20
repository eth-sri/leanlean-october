/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredPrimeDecomposition

/-! Separating prime components makes their filtered dimensions
additive up to a fixed degree shift. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {K σ ι : Type*} [Field K]

/-- Polynomial lifts independent on separate prime components remain
jointly independent after multiplying by the component separators. -/
private theorem prime_separator_lifts_independent
    [Fintype ι] [DecidableEq ι] (κ : ι → Type*) [∀ i, Fintype (κ i)]
    (I : Ideal (MvPolynomial σ K)) (P : ι → Ideal (MvPolynomial σ K))
    (hprime : ∀ i, (P i).IsPrime) (hIP : ∀ i, I ≤ P i)
    (a : ι → MvPolynomial σ K) (ha : ∀ i, a i ∉ P i)
    (hsep : ∀ i j, i ≠ j → a i ∈ P j)
    (v : ∀ i, κ i → MvPolynomial σ K)
    (hv : ∀ i, LinearIndependent K (fun j => (Ideal.Quotient.mkₐ K (P i)) (v i j))) :
    LinearIndependent K (fun t : Sigma κ =>
      (Ideal.Quotient.mkₐ K I) (a t.1 * v t.1 t.2)) := by
  classical
  let φ (i : ι)  :=
    Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ K (P i))
      (by solve_by_elim [Ideal.Quotient.eq_zero_iff_mem.mpr])
  have hφ (i : ι) (p : MvPolynomial σ K) :
      φ i ((Ideal.Quotient.mkₐ K I) p) = (Ideal.Quotient.mkₐ K _) p := rfl
  rw [Fintype.linearIndependent_iff]
  intro c hc t
  let i := t.1
  have hz (j : ι) (hji : j ≠ i)  :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hsep j i hji)
  have he := congrArg (φ i) hc
  simp only [map_sum, map_smul, hφ, map_mul, map_zero, Fintype.sum_sigma] at he
  have houter :
      (∑ j, ∑ k, c ⟨j, k⟩ •
        ((Ideal.Quotient.mkₐ K (P i)) (a j) * (Ideal.Quotient.mkₐ K _) (v j k))) =
      ∑ k, c ⟨i, k⟩ •
        ((Ideal.Quotient.mkₐ K _) (a i) * (Ideal.Quotient.mkₐ K _) (v i k)) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      simp [hz j hji]
    · simp
  rw [houter] at he
  have he' : (Ideal.Quotient.mkₐ K (P i)) (a i) *
      (∑ k, c ⟨i, k⟩ • (Ideal.Quotient.mkₐ K _) (v i k)) = 0 := by
    simpa [Finset.mul_sum, mul_smul_comm] using he
  have hsum := (mul_eq_zero.mp he').resolve_left (fun h => ha i (Ideal.Quotient.eq_zero_iff_mem.mp h))
  exact Fintype.linearIndependent_iff.mp (hv i) (fun k => c _) hsum t.2

variable [Finite σ]

/-- The sum of the component filtration dimensions injects into the
original coordinate filtration after a fixed shift independent of N. -/
private theorem prime_components_filtered_rank_lower [Fintype ι] [DecidableEq ι]
    (I : Ideal (MvPolynomial σ K)) (P : ι → Ideal (MvPolynomial σ K))
    (hprime : ∀ i, (P i).IsPrime) (hIP : ∀ i, I ≤ P i)
    (hanti : ∀ i j, P i ≤ P j → i = j) :
    ∃ D : ℕ, ∀ N : ℕ,
      (∑ i, Module.finrank K (filteredCoordinateSpace (P i) N)) ≤
        Module.finrank K (filteredCoordinateSpace I (D + N)) := by
  classical
  obtain ⟨a, ha, hsep⟩ := exists_prime_component_separators P hprime hanti
  let D := Finset.univ.sup (fun i => (a i).totalDegree)
  refine ⟨D, ?_⟩
  intro N
  choose v hvdeg hvlin using fun i => exists_filtered_polynomial_basis (P i) N
  let κ (i : ι) := Fin (Module.finrank K (filteredCoordinateSpace (P i) N))
  have hmem (t : Sigma κ) : (Ideal.Quotient.mkₐ K I) (a t.1 * v t.1 t.2) ∈
      filteredCoordinateSpace I (D + N) := by
    apply Submodule.mem_map.mpr
    refine ⟨a t.1 * v t.1 t.2, ?_, rfl⟩
    rw [mem_restrictTotalDegree]
    exact (totalDegree_mul _ _).trans (Nat.add_le_add
      (Finset.le_sup (f := fun i => (a i).totalDegree) (Finset.mem_univ t.1)) (hvdeg t.1 t.2))
  let w : Sigma κ → filteredCoordinateSpace I _ :=
    fun t => ⟨(Ideal.Quotient.mkₐ K I) _, hmem t⟩
  have hw : LinearIndependent K w :=
    LinearIndependent.of_comp (filteredCoordinateSpace I _).subtype (by apply prime_separator_lifts_independent <;> assumption)
  simpa [κ] using hw.fintype_card_le_finrank

/-- The dimension comparison for the canonical finite set of minimal primes,
with constructed separators. -/
theorem minimalPrimeComponents_filtered_rank_lower
    (I : Ideal (MvPolynomial σ K)) :
    ∃ D : ℕ, ∀ N : ℕ,
      (∑ P : minimalPrimeComponents I, Module.finrank K (filteredCoordinateSpace P.val N)) ≤
        Module.finrank K (filteredCoordinateSpace I (D + N)) := by
  classical
  apply prime_components_filtered_rank_lower I (fun P : minimalPrimeComponents I => P.val)
  · exact fun P => minimalPrimeComponents_isPrime P.property
  · exact fun P => le_minimalPrimeComponents P.property
  · intro P Q hPQ
    exact Subtype.ext (minimalPrimeComponents_eq_of_le P.property Q.property hPQ)

end
end CCDN
