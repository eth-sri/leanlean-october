module

public import OAI.LinearAlgebra.MatrixMultiplication.AllRings

public section

@[expose] section

/-! Proofs for a separately compiled frozen challenge. Never import Challenge here.
The sixth statement uses literal integer coefficient identities, not project
rank definitions or equality restricted to a finite set of field inputs. -/

namespace ComparatorChecks

open scoped BigOperators
open OAI.MatrixMultiplication

universe u

variable (R : Type u) [Ring R]

theorem omega_bound : Arithmetic.omega R ≤ (9 : ℝ) / 4 :=
  omega_le_nine_quarters_all_rings R

theorem admissible_nonempty : Set.Nonempty {τ : ℝ | Arithmetic.AdmissibleExponent R τ} :=
  ⟨_, admissibleExponent_nine_quarters_all_rings R⟩

theorem epsilon_cost (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : Arithmetic.MatrixAlgorithm R n n n,
        P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ ((9 : ℝ) / 4 + ε) :=
  admissibleExponent_nine_quarters_all_rings R ε hε

variable [Nontrivial R]

theorem admissible_bddBelow : BddBelow {τ : ℝ | Arithmetic.AdmissibleExponent R τ} :=
  ⟨2, fun _ => Arithmetic.admissibleExponent_two_le⟩

theorem omega_lower : (2 : ℝ) ≤ Arithmetic.omega R :=
  le_csInf (admissible_nonempty R) fun _ => Arithmetic.admissibleExponent_two_le

theorem exact_coefficients (ε : ℝ) (hε : 0 < ε) :
    ∃ n r : ℕ, 2 ≤ n ∧ (r : ℝ) ≤ (n : ℝ) ^ ((9 : ℝ) / 4 + ε) ∧
      ∃ (a b c : Fin r → (Fin n × Fin n) → ℤ),
        ∀ x y z : Fin n × Fin n,
          (if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0 : ℤ) =
            ∑ i, a i x * b i y * c i z :=
  by
    obtain ⟨n, r, hn, ⟨M, h⟩, hr⟩ :=
      AuxiliarySeparation.Integral.exists_integer_scheme hε
    rw [Foundation.Tensor.restrict_diagonal] at h
    exact ⟨n, r, hn, hr.le, M.left.transpose, M.middle.transpose, M.right.transpose,
      fun x y z => congrArg (· x y z) h⟩

end ComparatorChecks
