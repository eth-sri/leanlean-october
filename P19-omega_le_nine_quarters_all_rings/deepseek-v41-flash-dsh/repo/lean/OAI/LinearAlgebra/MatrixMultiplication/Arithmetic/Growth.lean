module

/-
Upstream source and modification notice
Adapted from OpenAI's matrix-multiplication sources (upstream `ComplexArithmetic/Growth.lean`,
omitted from this extraction) to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Complexity
public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Padding
public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.RecursiveBlockPrograms
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

public section

@[expose] section

namespace OAI

/-! Arithmetic programs over an arbitrary ring and asymptotic matrix multiplication costs. -/


namespace MatrixMultiplication.Arithmetic

open MatrixMultiplication.Foundation

variable {F : Type*} [Ring F]

theorem exists_power_cover {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) :
    ∃ k : ℕ, n ≤ b ^ k ∧ b ^ k ≤ b * n :=
  ⟨Nat.log b n + 1, (Nat.lt_pow_succ_log_self (by omega) n).le, by
    rw [pow_succ']
    exact Nat.mul_le_mul_left b (Nat.pow_log_le_self b (by omega))⟩

/-- A block-recursion step with ratio `R` and quadratic overhead `K` gives the
admissible exponent `τ` for every ring, via power-of-`b` sizes and padding. -/
theorem admissibleExponent_of_block_step {b R K : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 2 ≤ τ)
    (hR : (R : ℝ) ≤ (b : ℝ) ^ τ)
    (hstep : ∀ m : ℕ, ∀ P : MatrixAlgorithm F m m m, P.Correct →
      ∃ Q : MatrixAlgorithm F (b * m) (b * m) (b * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * m ^ 2) :
    AdmissibleExponent F τ := by
  intro ε hε
  have hb1 : 1 < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hb0 : (0 : ℝ) < b := by linarith
  have hq : (R : ℝ) < (b : ℝ) ^ (τ + ε) :=
    hR.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hb1 (by linarith))
  have hgap : 0 < (b : ℝ) ^ (τ + ε) - R := by linarith
  have hb2 : ((b : ℝ) ^ 2) ≤ (b : ℝ) ^ (τ + ε) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hb1.le (by push_cast; linarith)
  obtain ⟨C, hC1, hC2⟩ : ∃ C : ℝ, 1 ≤ C ∧ (R : ℝ) * C + K ≤ C * (b : ℝ) ^ (τ + ε)
  · refine ⟨(K : ℝ) / ((b : ℝ) ^ (τ + ε) - R) + 1, ?_, ?_⟩
    · have h2 : (0 : ℝ) ≤ (K : ℝ) / ((b : ℝ) ^ (τ + ε) - R) :=
        div_nonneg (Nat.cast_nonneg K) hgap.le
      linarith
    have hc : ((K : ℝ) / ((b : ℝ) ^ (τ + ε) - R) + 1) * ((b : ℝ) ^ (τ + ε) - R) =
        (K : ℝ) + ((b : ℝ) ^ (τ + ε) - R) := by
      rw [add_mul, div_mul_cancel₀ _ hgap.ne', one_mul]
    nlinarith
  have hCpos : (0 : ℝ) < C := by linarith
  have hpow : ∀ k, ∃ P : MatrixAlgorithm F (b ^ k) (b ^ k) (b ^ k), P.Correct ∧
      (P.cost : ℝ) ≤ C * (((b : ℝ) ^ (τ + ε)) ^ k) := by
    intro k
    induction k with
    | zero => exact ⟨scalarAlgorithm F, scalarAlgorithm_correct F, by simp [hC1]⟩
    | succ k ih =>
      obtain ⟨P, hP, hPc⟩ := ih
      obtain ⟨Q, hQ, hQc⟩ := hstep (b ^ k) P hP
      have hQc' : (Q.cost : ℝ) ≤ (R : ℝ) * P.cost + (K : ℝ) * (((b : ℝ) ^ k) ^ 2) := by
        push_cast
        exact_mod_cast hQc
      rw [show (((b : ℝ) ^ k) ^ 2) = (((b : ℝ) ^ 2) ^ k) by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]] at hQc'
      have hfin : (Q.cost : ℝ) ≤ C * (((b : ℝ) ^ (τ + ε)) ^ (k + 1)) := by
        calc (Q.cost : ℝ) ≤ (R : ℝ) * P.cost + (K : ℝ) * (((b : ℝ) ^ 2) ^ k) := hQc'
          _ ≤ (R : ℝ) * (C * (((b : ℝ) ^ (τ + ε)) ^ k)) +
                (K : ℝ) * (((b : ℝ) ^ (τ + ε)) ^ k) :=
              add_le_add (mul_le_mul_of_nonneg_left hPc (Nat.cast_nonneg R))
                (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb2 k)
                  (Nat.cast_nonneg K))
          _ = ((R : ℝ) * C + K) * (((b : ℝ) ^ (τ + ε)) ^ k) := by ring
          _ ≤ (C * (b : ℝ) ^ (τ + ε)) * (((b : ℝ) ^ (τ + ε)) ^ k) :=
              mul_le_mul_of_nonneg_right hC2 (pow_nonneg (by positivity) k)
          _ = C * (((b : ℝ) ^ (τ + ε)) ^ (k + 1)) := by ring
      exact (pow_succ' b k).symm ▸ ⟨Q, hQ, hfin⟩
  refine ⟨C * (b : ℝ) ^ (τ + ε), by positivity, fun n hn => ?_⟩
  obtain ⟨k, hnk, hkn⟩ := exists_power_cover hb hn
  obtain ⟨P, hP, hPc⟩ := hpow k
  obtain ⟨Q, hQ, hQP⟩ := MatrixAlgorithm.exists_restrict hnk hnk hnk P hP
  refine ⟨Q, hQ, (by exact_mod_cast hQP : (Q.cost : ℝ) ≤ (P.cost : ℝ)).trans ?_⟩
  refine hPc.trans ?_
  have h1 : (((b : ℝ) ^ (τ + ε)) ^ k) = ((b ^ k : ℕ) : ℝ) ^ (τ + ε) := by
    rw [Real.rpow_pow_comm hb0.le, Nat.cast_pow]
  have h3 : ((b : ℝ) * n) ^ (τ + ε) = ((b : ℝ) ^ (τ + ε)) * (n : ℝ) ^ (τ + ε) :=
    Real.mul_rpow hb0.le (Nat.cast_nonneg n)
  have h4 : ((b ^ k : ℕ) : ℝ) ^ (τ + ε) ≤ ((b : ℝ) * n) ^ (τ + ε) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hkn) (by linarith)
  rw [h1]
  calc C * ((b ^ k : ℕ) : ℝ) ^ (τ + ε) ≤ C * ((b : ℝ) * n) ^ (τ + ε) :=
        mul_le_mul_of_nonneg_left h4 hCpos.le
    _ = C * (b : ℝ) ^ (τ + ε) * (n : ℝ) ^ (τ + ε) := by rw [h3]; ring

/-- A fixed exact integer coefficient scheme gives the same arithmetic
exponent over every associative unital ring. -/
theorem admissibleExponent_of_int_rankAtMost {n r : ℕ} (hn : 2 ≤ n)
    (hRank : Tensor.RankAtMost (Tensor.matrixCoefficients (K := ℤ) (Fin n) (Fin n) (Fin n)) r)
    {τ : ℝ} (hτ : 2 ≤ τ) (hr : (r : ℝ) ≤ (n : ℝ) ^ τ) :
    AdmissibleExponent F τ := by
  apply admissibleExponent_of_block_step (K := 6 * r * n ^ 2) hn hτ hr
  intro m P hP
  obtain ⟨Q, hQ, hcost⟩ := RecursiveBlock.int_rank_block_step hRank P hP
  exact ⟨Q, hQ, by rw [hcost]; exact le_of_eq (by ring)⟩

/-- Arbitrarily close integer rank schemes imply the unchanged positive-slack
arithmetic exponent bound over every ring, including the zero ring. -/
theorem admissibleExponent_of_int_rank_bounds {τ : ℝ} (hτ : 2 ≤ τ)
    (hRank : ∀ ε : ℝ, 0 < ε → ∃ n r : ℕ, 2 ≤ n ∧
      Tensor.RankAtMost (Tensor.matrixCoefficients (K := ℤ) (Fin n) (Fin n) (Fin n)) r ∧
      (r : ℝ) ≤ (n : ℝ) ^ (τ + ε)) :
    AdmissibleExponent F τ := by
  intro ε hε
  obtain ⟨n, r, hn, hrank, hr⟩ := hRank (ε / 2) (half_pos hε)
  have hadm : AdmissibleExponent F (τ + ε / 2) :=
    admissibleExponent_of_int_rankAtMost hn hrank (by linarith) hr
  obtain ⟨C, hC, hcost⟩ := hadm (ε / 2) (half_pos hε)
  refine ⟨C, hC, fun m hm => ?_⟩
  obtain ⟨P, hP, hbound⟩ := hcost m hm
  exact ⟨P, hP, by
    rw [show τ + ε / 2 + ε / 2 = τ + ε by ring] at hbound
    exact hbound⟩

end MatrixMultiplication.Arithmetic


end OAI
