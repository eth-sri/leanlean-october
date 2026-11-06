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

/-- The dimension comparison for the canonical finite set of minimal primes,
with constructed separators. -/
theorem minimalPrimeComponents_filtered_rank_lower {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) :
    ∃ D : ℕ, ∀ N : ℕ,
      (∑ P : minimalPrimeComponents I, Module.finrank K (filteredCoordinateSpace P.val N)) ≤
        Module.finrank K (filteredCoordinateSpace I (D + N)) := by
  classical
  let ι := minimalPrimeComponents I
  let P : ι → Ideal (MvPolynomial σ K) := Subtype.val
  have hprime (i : ι) : (P i).IsPrime := minimalPrimeComponents_isPrime i.property
  have hIP (i : ι) : I ≤ P i := le_minimalPrimeComponents i.property
  have hanti (i j : ι) (h : P i ≤ P j) : i = j :=
    Subtype.ext (minimalPrimeComponents_eq_of_le i.property j.property h)
  obtain ⟨a, ha, hsep⟩ := exists_prime_component_separators P hprime hanti
  let D := Finset.univ.sup (fun i => (a i).totalDegree)
  refine ⟨D, fun N => ?_⟩
  choose v hvdeg hvlin using fun i => exists_filtered_polynomial_basis (P i) N
  let κ (i : ι) := Fin (Module.finrank K (filteredCoordinateSpace (P i) N))
  let φ (i : ι) : (MvPolynomial σ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ P i) :=
    Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ K (P i))
      (fun p hp => Ideal.Quotient.eq_zero_iff_mem.mpr (hIP i hp))
  have hφ (i : ι) (p : MvPolynomial σ K) :
      φ i ((Ideal.Quotient.mkₐ K I) p) = (Ideal.Quotient.mkₐ K (P i)) p :=
    congrArg (fun ψ : MvPolynomial σ K →ₐ[K] (MvPolynomial σ K ⧸ P i) => ψ p)
      (Ideal.Quotient.liftₐ_comp I (Ideal.Quotient.mkₐ K (P i))
        (fun p hp => Ideal.Quotient.eq_zero_iff_mem.mpr (hIP i hp)))
  have hlin : LinearIndependent K (fun t : Sigma κ =>
      (Ideal.Quotient.mkₐ K I) (a t.1 * v t.1 t.2)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc t
    let i := t.1
    have : (P i).IsPrime := hprime i
    have hane : (Ideal.Quotient.mkₐ K (P i)) (a i) ≠ 0 :=
      fun h => ha i (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have hz (j : ι) (hji : j ≠ i) : (Ideal.Quotient.mkₐ K (P i)) (a j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hsep j i hji)
    have he := congrArg (φ i) hc
    simp only [map_sum, map_smul, hφ, map_mul, map_zero, Fintype.sum_sigma] at he
    rw [Finset.sum_eq_single i (fun j _ hji => by
      simp only [hz j hji, zero_mul, smul_zero, Finset.sum_const_zero]) (by simp)] at he
    have he' : (Ideal.Quotient.mkₐ K (P i)) (a i) *
        (∑ k, c ⟨i, k⟩ • (Ideal.Quotient.mkₐ K (P i)) (v i k)) = 0 := by
      simpa only [Finset.mul_sum, mul_smul_comm] using he
    exact Fintype.linearIndependent_iff.mp (hvlin i) (fun k => c ⟨i, k⟩)
      ((mul_eq_zero.mp he').resolve_left hane) t.2
  have hmem (t : Sigma κ) : (Ideal.Quotient.mkₐ K I) (a t.1 * v t.1 t.2) ∈
      filteredCoordinateSpace I (D + N) := by
    refine Submodule.mem_map.mpr ⟨a t.1 * v t.1 t.2, ?_, rfl⟩
    rw [mem_restrictTotalDegree]
    exact (totalDegree_mul _ _).trans (Nat.add_le_add
      (Finset.le_sup (f := fun i => (a i).totalDegree) (Finset.mem_univ t.1)) (hvdeg t.1 t.2))
  let w : Sigma κ → filteredCoordinateSpace I (D + N) :=
    fun t => ⟨(Ideal.Quotient.mkₐ K I) (a t.1 * v t.1 t.2), hmem t⟩
  have hw : LinearIndependent K w :=
    LinearIndependent.of_comp (filteredCoordinateSpace I (D + N)).subtype hlin
  simpa only [Fintype.card_sigma, Fintype.card_fin, κ] using hw.fintype_card_le_finrank

end
end CCDN
