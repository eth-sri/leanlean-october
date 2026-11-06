/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.ForMathlib.StandardExponents
import CCDN.Hilbert.FilteredIntersection
import CCDN.ForMathlib.MvPolynomial
import CCDN.Hilbert.StandardMonomials

/-!
# Linear-growth monomial sets

A downward-closed exponent set with a linear counting bound cannot contain a
large square. Consequently its unbounded portions lie in coordinate rays.
-/

namespace CCDN
noncomputable section
open MvPolynomial

/-- Bounded exponent sets are finite. -/
instance finite_boundedStandardExponents {K σ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ) (N : ℕ) :
    Finite (Ideal.boundedStandardExponents I m N) := by
  classical
  let e := Finsupp.degreeLeEquivSym σ N
  let f : Ideal.boundedStandardExponents I m N → Sym (Option σ) N :=
    fun a => e ⟨a.val, a.property.2⟩
  apply Finite.of_injective f
  intro a b h
  have he := e.injective h
  apply Subtype.ext
  exact congrArg (fun p : {p : σ →₀ ℕ // p.degree ≤ N} => p.val) he

section
variable {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) {a : σ →₀ ℕ} {i j : σ}

/-- A standard monomial with two large exponents supplies an entire square of
independent quotient classes in degree at most `2B`. -/
theorem standard_square_le_filtered
    (B : ℕ)
    (ha : a ∈ Ideal.standardExponents I MonomialOrder.degLex)
    (hij : i ≠ j) (hi : B ≤ a i) (hj : B ≤ a j) :
    (B + 1) ^ 2 ≤ Module.finrank K (filteredCoordinateSpace I (2 * B)) := by
  let f : Fin (B + 1) × Fin (B + 1) →
      Ideal.boundedStandardExponents I MonomialOrder.degLex (2 * B) := fun t =>
    ⟨Finsupp.single i t.1.val + Finsupp.single j t.2.val, by
      constructor
      · apply Ideal.isLowerSet_standardExponents I MonomialOrder.degLex _ ha
        intro k
        by_cases hki : k = i
        · subst k
          simpa [hij, hij.symm] using (show t.1.val ≤ a i from by omega)
        by_cases hkj : k = j
        · subst k
          simpa [hij, hij.symm] using (show t.2.val ≤ a j from by omega)
        simp_all
      · change Finsupp.degree _ ≤ 2 * B
        rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
        omega⟩
  have hc := Nat.card_le_card_of_injective f (by
    intro s t h
    have hval := congrArg Subtype.val h
    have h1 := congrArg (fun a => a i) hval
    have h2 := congrArg (fun a => a j) hval
    simp [f, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hij, Finsupp.single_eq_of_ne hij.symm, add_zero, zero_add] at h1 h2
    grind)
  rw [← filteredCoordinateSpace_finrank_eq_standard_card I (2 * B)] at hc
  simpa [Nat.card_prod, Nat.card_fin, pow_two] using hc

/-- Under a linear Hilbert bound, at most one exponent can exceed a fixed
threshold. This excludes every two-dimensional monomial quadrant. -/
theorem standard_at_most_one_large
    (C : ℕ)
    (hbound : ∀ N ≥ 14, Module.finrank K (filteredCoordinateSpace I N) ≤ C * (N + 2))
    (ha : a ∈ Ideal.standardExponents I MonomialOrder.degLex)
    (hi : 2 * C + 14 ≤ a i) (hj : 2 * C + 14 ≤ a j) : i = j := by
  by_contra hij
  have hs := standard_square_le_filtered I (2 * C + 14) ha hij hi hj
  have hu := hbound (2 * (2 * C + 14)) (by omega)
  nlinarith

end

section
variable {σ : Type*} [Fintype σ] [DecidableEq σ] (B : ℕ) (j : σ) (b : σ → Fin B) (n : ℕ)

/-- A coordinate ray whose other coordinates lie in a finite box. -/
def exponentRay
    : σ →₀ ℕ :=
  (Finsupp.equivFunOnFinite.symm (fun k => (b k).val)).update j n

/-- The ray exponent `exponentRay B j b n` has coordinate `n` at `j` and coordinate `b k` at
every other `k`. -/
@[simp] lemma exponentRay_apply
    (k : σ) :
    exponentRay B j b n k = if k = j then n else (b k).val := by
  simp [exponentRay, Finsupp.update_apply, eq_comm]

end

