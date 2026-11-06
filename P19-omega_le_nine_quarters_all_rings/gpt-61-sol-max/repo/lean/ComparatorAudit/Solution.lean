module

public import OAI.LinearAlgebra.MatrixMultiplication.AllRings

@[expose] public section

/-! Proofs for a separately compiled frozen challenge. Never import Challenge here.
The sixth statement uses literal integer coefficient identities, not project
rank definitions or equality restricted to a finite set of field inputs. -/

namespace ComparatorChecks

open scoped BigOperators
universe u
open OAI.MatrixMultiplication

alias omega_bound := omega_le_nine_quarters_all_rings

alias admissible_bddBelow := Arithmetic.admissibleExponent_bddBelow
alias admissible_nonempty := Arithmetic.admissibleExponent_nonempty
alias omega_lower := Arithmetic.omega_two_le

theorem epsilon_cost (R : Type u) [Ring R] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : Arithmetic.MatrixAlgorithm R n n n,
        P.Correct ∧ (P.cost : ℝ) ≤
          C * (n : ℝ) ^ ((9 : ℝ) / 4 + ε) :=
  admissibleExponent_nine_quarters_all_rings R ε hε

theorem exact_coefficients (ε : ℝ) (hε : 0 < ε) :
    ∃ n r : ℕ, 2 ≤ n ∧ (r : ℝ) ≤ (n : ℝ) ^ ((9 : ℝ) / 4 + ε) ∧
      ∃ a b c : Fin r → Fin n × Fin n → ℤ,
        ∀ x y z : Fin n × Fin n,
          (if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0 : ℤ) =
            ∑ i, a i x * b i y * c i z :=
  by
    obtain ⟨n, hn, hr, hRank⟩ := AuxiliarySeparation.exists_exactMatrixRank_lt_rpow
      (τ := 9 / 4 + ε) (by
        linarith [AuxiliarySeparation.Integral.exactRankExponent_int_le_nine_quarters])
    refine ⟨n, AuxiliarySeparation.exactMatrixRank n, hn, hr.le, ?_⟩
    simpa only [Foundation.Tensor.RankAtMost, AuxiliarySeparation.matrixMultiplicationTensor,
      Foundation.Tensor.matrixCoefficients, Foundation.Tensor.rankOne, funext_iff] using hRank

end ComparatorChecks
