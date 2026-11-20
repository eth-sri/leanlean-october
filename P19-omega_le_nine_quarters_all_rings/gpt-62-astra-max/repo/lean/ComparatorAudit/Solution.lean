module

public import OAI.LinearAlgebra.MatrixMultiplication.AllRings

public section

@[expose] section

/-! Proofs for a separately compiled frozen challenge. Never import Challenge here.
The sixth statement uses literal integer coefficient identities, not project
rank definitions or equality restricted to a finite set of field inputs. -/

namespace ComparatorChecks

open scoped BigOperators
universe u
open OAI.MatrixMultiplication

alias omega_bound := omega_le_nine_quarters_all_rings

alias admissible_bddBelow := Arithmetic.admissibleExponent_bddBelow

theorem admissible_nonempty (R : Type u) [Ring R] :
    Set.Nonempty {τ : ℝ | Arithmetic.AdmissibleExponent R τ} :=
  ⟨_, admissibleExponent_nine_quarters_all_rings R⟩

theorem omega_lower (R : Type u) [Ring R] [Nontrivial R] :
    (2 : ℝ) ≤ Arithmetic.omega R :=
  le_csInf (admissible_nonempty R) fun _ => Arithmetic.admissibleExponent_two_le

alias epsilon_cost := matrix_multiplication_cost_le_nine_quarters_all_rings

theorem exact_coefficients (ε : ℝ) (hε : 0 < ε) :
    ∃ n r : ℕ, 2 ≤ n ∧ (r : ℝ) ≤ (n : ℝ) ^ ((9 : ℝ) / 4 + ε) ∧
      ∃ a b c : Fin r → Fin n × Fin n → ℤ,
        ∀ x y z : Fin n × Fin n,
          (if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0 : ℤ) =
            ∑ i, a i x * b i y * c i z :=
  AuxiliarySeparation.finite_blocks (lt_add_of_le_of_pos AuxiliarySeparation.Integral.exactRankExponent_int_le_nine_quarters hε)

end ComparatorChecks
