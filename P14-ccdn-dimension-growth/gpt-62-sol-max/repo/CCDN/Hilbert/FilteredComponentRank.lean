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

/-- Polynomial lifts independent on separate prime components remain
jointly independent after multiplying by the component separators. -/
private theorem prime_separator_lifts_independent {K σ ι : Type*} [Field K]
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
  rw [Fintype.linearIndependent_iff]
  rintro c hc ⟨i, k⟩
  let q := Ideal.Quotient.mkₐ K (P i)
  have he := congrArg (Ideal.Quotient.factorₐ K (hIP i)) hc
  simp only [map_sum, map_smul, map_zero, map_mul, ← AlgHom.comp_apply, Ideal.Quotient.factorₐ_comp_mk,
    Fintype.sum_sigma] at he
  rw [Finset.sum_eq_single i] at he
  · have hqi : q (a i) ≠ 0 := fun h => ha i (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have hs : q (a i) * ∑ j, c ⟨i, j⟩ • q (v i j) = 0 := by
      simpa only [Finset.mul_sum, mul_smul_comm] using he
    exact Fintype.linearIndependent_iff.mp (hv i) _ ((mul_eq_zero.mp hs).resolve_left hqi) k
  · intro j _ hj
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr (hsep j i hj)]
  · simp

/-- The sum of the component filtration dimensions injects into the
original coordinate filtration after a fixed shift independent of N. -/
theorem prime_components_filtered_rank_lower {K σ ι : Type*} [Field K]
    [Finite σ] [Fintype ι]
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
  have hlin := prime_separator_lifts_independent κ I P hprime hIP a ha hsep v hvlin
  have hmem (t : Sigma κ) : (Ideal.Quotient.mkₐ K I) (a t.1 * v t.1 t.2) ∈
      filteredCoordinateSpace I (D + N) := by
    refine mem_filteredCoordinateSpace.mpr ⟨a t.1 * v t.1 t.2, ?_, rfl⟩
    exact (totalDegree_mul _ _).trans (Nat.add_le_add
      (Finset.le_sup (f := fun i => (a i).totalDegree) (Finset.mem_univ t.1)) (hvdeg t.1 t.2))
  let w : Sigma κ → filteredCoordinateSpace I (D + N) :=
    fun t => ⟨(Ideal.Quotient.mkₐ K I) (a t.1 * v t.1 t.2), hmem t⟩
  have hw : LinearIndependent K w :=
    LinearIndependent.of_comp (filteredCoordinateSpace I (D + N)).subtype hlin
  simpa only [Fintype.card_sigma, Fintype.card_fin, κ] using hw.fintype_card_le_finrank

end
end CCDN
