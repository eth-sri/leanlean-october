/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hilbert.FilteredPrimeDecomposition
import CCDN.Algebra.BinomialSectionBound
import CCDN.Hilbert.FilteredComponentRank

/-! Additivity of the leading filtered dimension bounds the total degree of
the minimal-prime components of a two-equation section. -/

namespace CCDN
section
open MvPolynomial

/-- A common linear upper bound bounds the sum of the eventual linear
slopes of the minimal-prime components. -/
theorem minimalPrimeComponents_slope_sum_le {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (C N₀ : ℕ)
    (hupper : ∀ N ≥ N₀, Module.finrank K (filteredCoordinateSpace I N) ≤ C * (N + 1))
    (d : minimalPrimeComponents I → ℕ)
    (hdegree : ∀ P, HasFilteredCurveDegree P.val (d P)) :
    ∑ P, d P ≤ C := by
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ∀ N : ℕ,
      (∑ P : minimalPrimeComponents I, Module.finrank K (filteredCoordinateSpace P.val N)) ≤
        Module.finrank K (filteredCoordinateSpace I (D + N)) := by
    apply prime_components_filtered_rank_lower I (fun P : minimalPrimeComponents I => P.val)
    · exact fun P => (mem_minimalPrimeComponents.mp P.property).isPrime
    · exact fun P => le_minimalPrimeComponents P.property
    · intro P Q hPQ
      exact Subtype.ext ((mem_minimalPrimeComponents.mp Q.property).eq_of_le (mem_minimalPrimeComponents.mp P.property).prop hPQ)
  choose Nᵢ cᵢ hNᵢ using hdegree
  let Nmax := Finset.univ.sup Nᵢ
  let c := ∑ P, cᵢ P
  let E := ∑ P, d P
  have hsum (N : ℕ) (hN : Nmax ≤ N) :
      ((∑ P : minimalPrimeComponents I,
          Module.finrank K (filteredCoordinateSpace P.val N) : ℕ) : ℤ) =
        (E : ℤ) * N + c := by
    push_cast
    calc
      _ = ∑ P, ((d P : ℤ) * N + cᵢ P) := by
        apply Finset.sum_congr rfl
        intro P _
        exact hNᵢ P N ((Finset.le_sup (Finset.mem_univ P)).trans hN)
      _ = _ := by
        simp [Finset.sum_add_distrib, ← Finset.sum_mul, E, c, Nat.cast_sum]
  by_contra h
  have hbig : C + 1 ≤ E := by grind
  let N := C * (D + 1) + c.natAbs + Nmax + N₀ + 1
  have hNmax : Nmax ≤ N := by grind
  have hbound := (hD N).trans (hupper (D + N) (by grind))
  have hboundZ : E * N + c ≤ C * (D + N + 1) := by
    rw [← hsum N hNmax]
    exact_mod_cast hbound
  have hmul : ((C : ℤ) + 1) * N ≤ (E : ℤ) * N := by nlinarith
  have hc : -(c.natAbs : ℤ) ≤ c := by omega
  have hNeq : (N : ℤ) = C * (D + 1) + c.natAbs + Nmax + N₀ + 1 := by grind
  nlinarith

