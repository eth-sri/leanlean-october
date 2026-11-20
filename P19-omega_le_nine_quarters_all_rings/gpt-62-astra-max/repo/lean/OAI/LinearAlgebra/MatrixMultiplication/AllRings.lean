module

/-
Copyright (c) 2026. Released under Apache-2.0 as described in LICENSE.
Integral extension of OpenAI's matrix-multiplication proof and its all-fields
extension. See UPSTREAM.md for provenance and attribution.
-/

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Price.Detection
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Estimates
public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Growth
public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.LowerBound

@[expose] public noncomputable section

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

/-- The exact integer coefficient rank exponent is at most `9/4`.
Both finite separation and convolution bounds are supplied by proved integral
constructions, with no field or algebraic-closure hypothesis. -/
theorem exactRankExponent_int_le_nine_quarters :
    exactRankExponent ℤ ≤ (9 : ℝ) / 4 := by
  apply rpow_exponent_le_of_nat_bound (C := 2)
  intro d hd
  let v := (d:ℝ)^(9/4:ℝ)
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hv : 1 ≤ v := Real.one_le_rpow hd' (by norm_num)
  by_contra! h
  obtain ⟨χ,hχ⟩ := exists_detecting_price (k := ⌊v⌋₊+1) hd (by omega) (by
    push_cast; linarith [Nat.floor_le (by linarith : 0 ≤ v)])
  have hb := (χ.scalar_fourth (k := ⌊v⌋₊+1) (by omega)).trans ((Odd.pow_le_pow (by decide : Odd 3)).mpr hχ)
  have he : v^4 = ((d:ℝ)^3)^3 := by
    dsimp [v]; rw [← Real.rpow_mul_natCast (by positivity)]; norm_num; ring
  push_cast at hb; linarith [pow_lt_pow_left₀ (Nat.lt_floor_add_one v) (by positivity : 0 ≤ v) (by decide : 4 ≠ 0)]

end AuxiliarySeparation.Integral

/-- Every ring admits the positive-slack arithmetic bound at exponent `9/4`.
This statement also includes the zero ring. -/
theorem admissibleExponent_nine_quarters_all_rings (R : Type u) [Ring R] :
    Arithmetic.AdmissibleExponent R ((9 : ℝ) / 4) := by
  intro ε hε
  let α := AuxiliarySeparation.exactRankExponent ℤ
  have h : α ≤ 9/4 := AuxiliarySeparation.Integral.exactRankExponent_int_le_nine_quarters
  simpa [α] using AuxiliarySeparation.Integral.exactRankExponent_int_admissible R (9/4+ε-α) (by linarith)

/-- The square matrix multiplication exponent over every associative unital
ring is at most `9/4`. In the trivial case the existing infimum definition
returns zero; the substantive integer-rank argument covers nontrivial rings. -/
theorem omega_le_nine_quarters_all_rings (R : Type u) [Ring R] :
    Arithmetic.omega R ≤ (9 : ℝ) / 4 := by
  unfold Arithmetic.omega
  by_cases h : BddBelow {τ : ℝ | Arithmetic.AdmissibleExponent R τ}
  · exact csInf_le h (admissibleExponent_nine_quarters_all_rings R)
  · rw [Real.sInf_of_not_bddBelow h]
    norm_num

/-- For each positive slack there is one constant valid for every matrix size,
and division-free arithmetic programs with the original gate-count model. -/
theorem matrix_multiplication_cost_le_nine_quarters_all_rings
    (R : Type u) [Ring R] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : Arithmetic.MatrixAlgorithm R n n n,
        P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ ((9 : ℝ) / 4 + ε) :=
  admissibleExponent_nine_quarters_all_rings R ε hε

end OAI.MatrixMultiplication
