/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Hilbert.PolynomialComparison
import CCDN.Algebra.CoordinatePowerGeneration
public import Mathlib.RingTheory.Algebraic.Defs
import CCDN.Hilbert.FunctionFieldRank
import CCDN.Hilbert.StandardMonomials
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! Eventual linearity follows by comparing the Hilbert polynomial with a linear bound. -/

public section
namespace CCDN

variable {K σ : Type*} [Field K] [Fintype σ]
open Polynomial

/-- An eventual linear upper bound on a filtered coordinate ring implies an
eventually affine Hilbert function with natural slope. -/
theorem filteredCoordinateSpace_eventually_linear [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) (C T : ℕ)
    (hbound : ∀ N ≥ T, Module.finrank K (filteredCoordinateSpace I N) ≤ C * (N + 2)) :
    ∃ d, HasFilteredCurveDegree I d := by
  classical
  by_cases hI : I = ⊤
  · subst I
    refine ⟨0, 0, 0, ?_⟩
    intro M _
    rw [Module.finrank_zero_of_subsingleton]
    simp
  let P := filteredHilbertPolynomial I
  have hdeg : P.natDegree ≤ 1 := by
    apply (polynomial_natDegree_le_of_eventual_nat_eval_le P
      (Polynomial.C (C : ℚ) * (X + Polynomial.C 2)) (filteredHilbertPolynomial_leadingCoeff_pos I hI) ?_).trans
      (by compute_degree)
    obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec I
    refine ⟨max M T, fun n hn => ?_⟩
    rw [show P.eval (n : ℚ) = _ from hM n (by omega)]
    simpa only [eval_mul, eval_C, eval_add, eval_X, Nat.cast_mul, Nat.cast_add,
      Nat.cast_ofNat] using (Nat.cast_le (α := ℚ)).mpr (hbound n (by omega))
  obtain ⟨a, b, hP⟩ := exists_eq_X_add_C_of_natDegree_le_one hdeg
  obtain ⟨N, hN⟩ := filteredHilbertPolynomial_spec I
  let H := fun n => Module.finrank K (filteredCoordinateSpace I n)
  have hspec (n : ℕ) (hn : N ≤ n) : a * n + b = (H n : ℚ) := by
    aesop
  let d := H (N + 1) - H N
  have hdq : (d : ℚ) = a := by
    have hmono : H N ≤ H (N + 1) :=
      Submodule.finrank_mono (filteredCoordinateSpace_mono I (by omega))
    dsimp [d]
    rw [Nat.cast_sub hmono]
    have h₀ := hspec N le_rfl
    have h₁ := hspec (N + 1) (by omega)
    push_cast at h₁
    linarith
  have hformula (k : ℕ) : H (N + k) = H N + d * k := by
    apply Nat.cast_injective (R := ℚ)
    push_cast
    rw [hdq]
    have h₀ := hspec N le_rfl
    have h₁ := hspec (N + k) (by omega)
    push_cast at h₁
    nlinarith
  refine ⟨d, N, (H N : ℤ) - d * N, ?_⟩
  intro n hn
  have he := hformula (n - N)
  rw [Nat.add_sub_of_le hn] at he
  change (H n : ℤ) = _
  rw [he]
  push_cast
  rw [Nat.cast_sub hn]
  ring

/-- A transcendental coordinate contributes all of its powers to the filtration. -/
theorem transcendental_coordinate_filtered_lower 
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

end CCDN
