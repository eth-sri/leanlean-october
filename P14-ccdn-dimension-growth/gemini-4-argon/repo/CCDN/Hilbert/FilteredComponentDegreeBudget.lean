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

/-- The additive degree inequality in the rational curve-degree interface. -/
theorem polynomialSection_minimalPrime_curveDegree_sum_le
    (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g)
    (d : minimalPrimeComponents (polynomialSectionIdeal f g) → ℕ)
    (hdegree : ∀ P, HasAffineCurveDegree P.val (d P)) :
    ∑ P, d P ≤ f.totalDegree * g.totalDegree := by
  classical
  let I := polynomialSectionIdeal f g
  let C := f.totalDegree * g.totalDegree
  let N₀ := f.totalDegree + g.totalDegree
  have hupper (N : ℕ) (hN : N₀ ≤ N) :
      Module.finrank ℚ (filteredCoordinateSpace I N) ≤ C * (N + 1) := by
    simpa only [Nat.choose_one_right, Nat.add_comm 1, I, C] using
      filteredCoordinateSpace_codim_two_bound (n := 1) hf.prime hfg I
        (polynomialSectionIdeal_first_mem f g) (polynomialSectionIdeal_second_mem f g) hN
  obtain ⟨D, hD⟩ := minimalPrimeComponents_filtered_rank_lower I
  choose Nᵢ cᵢ hNᵢ using hdegree
  let Nmax := Finset.univ.sup Nᵢ
  let c := ∑ P, cᵢ P
  let E := ∑ P, d P
  have hsum (N : ℕ) (hN : Nmax ≤ N) :
      ((∑ P : minimalPrimeComponents I,
          Module.finrank ℚ (filteredCoordinateSpace P.val N) : ℕ) : ℤ) =
        (E : ℤ) * N + c := by
    push_cast
    calc
      _ = ∑ P, ((d P : ℤ) * N + cᵢ P) := Finset.sum_congr rfl fun P _ =>
        hNᵢ P N ((Finset.le_sup (Finset.mem_univ P)).trans hN)
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.sum_mul, E, c, Nat.cast_sum]
  by_contra h
  have hbig : C + 1 ≤ E := by dsimp only [E, C]; omega
  let N := C * (D + 1) + c.natAbs + Nmax + N₀ + 1
  have hNmax : Nmax ≤ N := by dsimp only [N]; omega
  have hNN₀ : N₀ ≤ D + N := by dsimp only [N]; omega
  have hboundZ : (E : ℤ) * N + c ≤ (C : ℤ) * (D + N + 1) := by
    rw [← hsum N hNmax]
    exact_mod_cast (hD N).trans (hupper (D + N) hNN₀)
  have hmul : ((C : ℤ) + 1) * N ≤ (E : ℤ) * N := by
    exact_mod_cast Nat.mul_le_mul_right N hbig
  have hc : -(c.natAbs : ℤ) ≤ c := by
    have hh : -c ≤ ((-c).natAbs : ℤ) := Int.le_natAbs
    rw [Int.natAbs_neg] at hh; omega
  have hNeq : (N : ℤ) = C * (D + 1) + c.natAbs + Nmax + N₀ + 1 := by
    dsimp only [N]; push_cast; rfl
  nlinarith

end
end CCDN
