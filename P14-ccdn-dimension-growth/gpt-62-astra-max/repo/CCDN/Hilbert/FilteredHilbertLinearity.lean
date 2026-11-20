/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Hilbert.PolynomialComparison
import CCDN.Algebra.CoordinatePowerGeneration
import CCDN.Hilbert.FunctionFieldRank
public import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.ComputeDegree
import Mathlib.LinearAlgebra.Dimension.Finite

/-! Compare the Hilbert polynomial with a linear upper bound, and bound the
filtered rank from below by powers of a transcendental coordinate. -/

@[expose] public section
namespace CCDN
noncomputable section

variable {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]

/-- The Hilbert polynomial of a proper quotient with at most linear growth is
affine. Taking a first difference in the stable range gives its integral slope. -/
theorem curve_degree_of_linear_growth (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤) (C T : ℕ)
    (hbound : ∀ N ≥ T, Module.finrank K (filteredCoordinateSpace I N) ≤ C * (N + 2)) :
    ∃ d, HasFilteredCurveDegree I d := by
  let P := filteredHilbertPolynomial I
  let H (n : ℕ) := Module.finrank K (filteredCoordinateSpace I n)
  obtain ⟨N, hN⟩ := filteredHilbertPolynomial_spec I
  have hdeg : P.natDegree ≤ 1 := by
    let Q : Polynomial ℚ := Polynomial.C (C : ℚ) * (Polynomial.X + 2)
    apply (polynomial_natDegree_le_of_eventual_nat_eval_le P Q
      (filteredHilbertPolynomial_leadingCoeff_pos I hI) ?_).trans
    · dsimp [Q]; compute_degree
    · refine ⟨max N T, fun n hn => ?_⟩
      rw [show P.eval (n : ℚ) = H n from hN n (by omega)]
      simpa [Q] using (show (H n : ℚ) ≤ (C : ℚ) * (n + 2) by exact_mod_cast hbound n (by omega))
  obtain ⟨a, b, he⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hdeg
  have h (n : ℕ) (hn : N ≤ n) : a * n + b = H n := by
    have h : P.eval (n : ℚ) = H n := hN n hn
    simpa [he] using h
  let d := H (N + 1) - H N
  have hmono : H N ≤ H (N + 1) := Submodule.finrank_mono (filteredCoordinateSpace_mono I (by omega))
  have hd : (d : ℚ) = a := by dsimp [d]; rw [Nat.cast_sub hmono, ← h _ (by omega), ← h _ le_rfl]; push_cast; ring
  refine ⟨d, N, (H N : ℤ) - d * N, fun m hm => ?_⟩
  change (H m : ℤ) = _
  exact_mod_cast (show (H m : ℚ) = d * m + (H N - (d : ℚ) * N) by rw [hd, ← h _ hm, ← h _ le_rfl]; ring)

/-- A transcendental coordinate contributes all of its powers to the filtration. -/
theorem transcendental_coordinate_filtered_lower {K σ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) {j : σ}
    (hj : Transcendental K ((Ideal.Quotient.mk I) (MvPolynomial.X j))) (N : ℕ) :
    N + 1 ≤ Module.finrank K (filteredCoordinateSpace I N) := by
  classical
  have hlin := transcendental_powers_independent
    ((Ideal.Quotient.mk I) (MvPolynomial.X j)) hj (N + 1)
  have hmem (k : Fin (N + 1)) :
      ((Ideal.Quotient.mk I) (MvPolynomial.X j)) ^ k.val ∈ filteredCoordinateSpace I N := by
    apply Submodule.mem_map.mpr
    refine ⟨MvPolynomial.X j ^ k.val, ?_, by simp⟩
    rw [MvPolynomial.mem_restrictTotalDegree, MvPolynomial.totalDegree_X_pow]
    omega
  let v : Fin (N + 1) → filteredCoordinateSpace I N :=
    fun k => ⟨((Ideal.Quotient.mk I) (MvPolynomial.X j)) ^ k.val, hmem k⟩
  have hv : LinearIndependent K v :=
    LinearIndependent.of_comp (filteredCoordinateSpace I N).subtype hlin
  simpa using hv.fintype_card_le_finrank

end
end CCDN
