module

/-
Copyright (c) 2026. Released under Apache-2.0 as described in LICENSE.
Integral extension of OpenAI's matrix-multiplication proof and its all-fields
extension. See UPSTREAM.md for provenance and attribution.
-/

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.Inequalities
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Basic
public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Compiler
public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.LowerBound

public section

@[expose] section

/-!
# Matrix multiplication over every ring

Exact integer coefficient schemes give the bound `9/4` over every associative
unital ring, including noncommutative rings. The arithmetic exponent uses the
same program semantics, gate costs, positive slack, and infimum as the prior
all-fields theorem. For nontrivial rings its admissible-exponent set is bounded
below. For trivial rings multiplication has zero arithmetic cost, and the
real-valued infimum is zero by Mathlib's convention for an unbounded-below set.

The direct operation-count theorem also includes the zero ring. Its exponent
is `9/4 + ε` for every positive `ε`; it does not assert an exact `O(n^(9/4))`
operation bound or a uniform circuit-generation algorithm.
-/

namespace OAI.MatrixMultiplication

universe u

namespace AuxiliarySeparation.Integral

open Foundation

/-- The exact rank exponent is detected up to integer rounding. -/
theorem exactRankExponent_int_le_nine_quarters :
    exactRankExponent ≤ (9 : ℝ) / 4 := by
  apply rpow_exponent_le_of_nat_bound (C := 2)
  intro d hd
  let y := (d : ℝ) ^ (9/4 : ℝ)
  have hy : 1 ≤ y := Real.one_le_rpow (Nat.one_le_cast.mpr hd) (by norm_num)
  by_contra! H
  have hk : ((⌊y⌋₊+1 : ℕ) : ℝ) < (d : ℝ) ^ exactRankExponent := by
    push_cast
    linarith [Nat.floor_le (zero_le_one.trans hy)]
  obtain ⟨χ, hχ⟩ := exists_detecting_character hd hk
  rw [χ.value_matrixMultiplication hd] at hχ
  have h := Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hd) χ.exponent_le_nine_quarters
  have hχ' := NNReal.coe_le_coe.mpr hχ
  push_cast at hχ'
  linarith [Nat.lt_floor_add_one y]

/-- Finite integer schemes witness the rank bound with any positive slack. -/
theorem exists_integer_scheme {ε : ℝ} (hε : 0 < ε) :
    ∃ n r : ℕ, 2 ≤ n ∧ Tensor.RankAtMost (Tensor.squareCoefficients n) r ∧
      (r : ℝ) < (n : ℝ) ^ ((9 : ℝ) / 4 + ε) := by
  obtain ⟨n, r, hn, h, hr⟩ := exists_near_optimal_block
    (exactRankExponent_int_le_nine_quarters.trans_lt (lt_add_of_pos_right _ hε))
  rw [← TensorSemiring.squareCoefficients_class] at h
  exact ⟨n, r, hn, (TensorSemiring.classOf_le_nat_iff_rankAtMost _ _).mp h, hr⟩

end AuxiliarySeparation.Integral

/-- The positive-slack arithmetic bound, including the zero ring. -/
theorem admissibleExponent_nine_quarters_all_rings (R : Type u) [Ring R] :
    Arithmetic.AdmissibleExponent R ((9 : ℝ) / 4) := by
  intro ε hε
  obtain ⟨n, r, hn, h, hr⟩ := AuxiliarySeparation.Integral.exists_integer_scheme hε
  exact Arithmetic.cost_bound_of_int_scheme hn h (by linarith) hr

/-- The admissible bound also bounds the infimum, with zero as the
convention for an unbounded-below set. -/
theorem omega_le_nine_quarters_all_rings (R : Type u) [Ring R] :
    Arithmetic.omega R ≤ (9 : ℝ) / 4 := by
  by_cases h : BddBelow {τ : ℝ | Arithmetic.AdmissibleExponent R τ}
  · exact csInf_le h (admissibleExponent_nine_quarters_all_rings R)
  · rw [Arithmetic.omega, Real.sInf_of_not_bddBelow h]
    norm_num

end OAI.MatrixMultiplication
