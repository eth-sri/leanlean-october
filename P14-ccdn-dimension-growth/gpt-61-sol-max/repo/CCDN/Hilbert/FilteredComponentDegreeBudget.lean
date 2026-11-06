/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Hilbert.FilteredPrimeDecomposition
import CCDN.Algebra.BinomialSectionBound
import CCDN.Hilbert.FilteredComponentRank

/-! Additivity of the leading filtered dimension bounds the total degree of
the minimal-prime components of a two-equation section. -/

public section
namespace CCDN
open MvPolynomial

/-- A common linear upper bound bounds the sum of the eventual linear
slopes of the minimal-prime components. -/
private theorem minimalPrimeComponents_slope_sum_le {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (C N₀ : ℕ)
    (hupper : ∀ N ≥ N₀, Module.finrank K (filteredCoordinateSpace I N) ≤ C * (N + 1))
    (d : minimalPrimeComponents I → ℕ)
    (hdegree : ∀ P, HasFilteredCurveDegree P.val (d P)) :
    ∑ P, d P ≤ C := by
  classical
  obtain ⟨D, hD⟩ := minimalPrimeComponents_filtered_rank_lower I
  choose Nᵢ cᵢ hNᵢ using hdegree
  let Nmax := Finset.univ.sup Nᵢ
  let c := ∑ P, cᵢ P
  let E := ∑ P, d P
  have hsum (N : ℕ) (hN : Nmax ≤ N) :
      ((∑ P : minimalPrimeComponents I,
          Module.finrank K (filteredCoordinateSpace P.val N) : ℕ) : ℤ) =
        ↑E * N + c := by
    push_cast
    calc
      _ = ∑ P, ((d P : ℤ) * N + cᵢ P) := by
        apply Finset.sum_congr rfl
        intro P _
        exact hNᵢ P N ((Finset.le_sup (Finset.mem_univ P)).trans hN)
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, E, c, Nat.cast_sum]
  by_contra h
  have hbig : C + 1 ≤ E := by dsimp only [E]; omega
  let N := C * (D + 1) + c.natAbs + Nmax + N₀ + 1
  have hNmax : Nmax ≤ N := by dsimp only [N]; omega
  have hNN₀ : N₀ ≤ D + N := by dsimp only [N]; omega
  have hbound := (hD N).trans (hupper (D + N) hNN₀)
  have hboundZ : ↑E * N + c ≤ ↑C * (D + N + 1) := by
    rw [← hsum N hNmax]
    exact_mod_cast hbound
  have hc : -↑c.natAbs ≤ c := by
    omega
  have hNeq : (N : ℤ) = C * (D + 1) + c.natAbs + Nmax + N₀ + 1 := rfl
  nlinarith


/-- The additive degree inequality in the rational curve-degree interface. -/
theorem polynomialSection_minimalPrime_curveDegree_sum_le
    (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g)
    (d : minimalPrimeComponents (polynomialSectionIdeal f g) → ℕ)
    (hdegree : ∀ P, HasAffineCurveDegree P.val (d P)) :
    ∑ P, d P ≤ f.totalDegree * g.totalDegree :=
  (by
    let inline_hf := Irreducible.prime hf
    apply minimalPrimeComponents_slope_sum_le (polynomialSectionIdeal f g)
      (f.totalDegree * g.totalDegree) (f.totalDegree + g.totalDegree) _ d hdegree
    intro N hN
    have hh := filteredCoordinateSpace_codim_two_bound  inline_hf hfg
      (polynomialSectionIdeal f g) (polynomialSectionIdeal_first_mem f g)
      (polynomialSectionIdeal_second_mem f g) hN
    simpa only [Nat.choose_one_right, Nat.add_comm 1] using hh)

end CCDN
