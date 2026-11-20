/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredIntersection

/-!
# The affine Hilbert degree of a curve

An affine algebraic set is represented by an ideal in `ℚ[x₁,…,xₙ]`. For an integral curve,
its degree is the slope of the eventually linear affine Hilbert function: the dimension
of polynomials of total degree at most `M` in its coordinate ring is `d*M + c` for large `M`.
The slope of an eventually linear function is unique, and a pointwise inequality between two
eventually linear functions compares their slopes (`eventual_linear_slope_le`).
-/

@[expose] public section

namespace CCDN

/-- The polynomial ring `ℚ[x₁, …, xₙ]` in which affine algebraic sets are cut out. -/
abbrev CoordinatePolynomial (n : ℕ) := MvPolynomial (Fin n) ℚ

/-- The affine Hilbert function: the dimension of the polynomials of total degree at
most `M` in the coordinate ring. -/
noncomputable def affineHilbertFunction {n : ℕ} (I : Ideal (CoordinatePolynomial n))
    (M : ℕ) : ℕ := Module.finrank ℚ (filteredCoordinateSpace I M)

/-- Degree via the eventual affine Hilbert polynomial. This condition is mathematical
data about the coordinate ring, and contains no point-counting estimate. -/
def HasAffineCurveDegree {n : ℕ} (I : Ideal (CoordinatePolynomial n)) (d : ℕ) : Prop :=
  ∃ N : ℕ, ∃ c : ℤ, ∀ M : ℕ, N ≤ M →
    (affineHilbertFunction I M : ℤ) = (d : ℤ) * M + c

/-- Eventual domination of eventually linear functions compares their slopes. -/
lemma eventual_linear_slope_le (f g : ℕ → ℕ) (a b : ℕ)
    (hf : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N, (f n : ℤ) = (a : ℤ) * n + c)
    (hg : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N, (g n : ℤ) = (b : ℤ) * n + c)
    (T : ℕ) (hle : ∀ n ≥ T, f n ≤ g n) : a ≤ b := by
  obtain ⟨N₀, c, hc⟩ := hf
  obtain ⟨N₁, e, he⟩ := hg
  by_contra hbad
  have hab : b + 1 ≤ a := by omega
  let N := T + N₀ + N₁ + c.natAbs + e.natAbs + 1
  have hN₀ : N₀ ≤ N := by omega
  have hN₁ : N₁ ≤ N := by omega
  have hh : (a : ℤ) * N + c ≤ (b : ℤ) * N + e := by
    rw [← hc N hN₀, ← he N hN₁]
    exact_mod_cast hle N (by dsimp [N]; omega)
  have hmul : ((b : ℤ) + 1) * N ≤ (a : ℤ) * N := by
    exact_mod_cast Nat.mul_le_mul_right N hab
  
  
  grind

end CCDN
