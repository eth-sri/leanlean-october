module

public import OAI.LinearAlgebra.MatrixMultiplication.AllRings

public section

@[expose] section

namespace ComparatorChecks

open scoped BigOperators
universe u
open OAI.MatrixMultiplication

theorem epsilon_cost (R : Type u) [Ring R] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : Arithmetic.MatrixAlgorithm R n n n,
        P.Correct ∧ (P.cost : ℝ) ≤
          C * (n : ℝ) ^ ((9 : ℝ) / 4 + ε) :=
  Arithmetic.admissibleExponent_nine_quarters R ε hε

theorem admissible_nonempty (R : Type u) [Ring R] :
    Set.Nonempty {τ : ℝ | Arithmetic.AdmissibleExponent R τ} :=
  ⟨(9 : ℝ) / 4, epsilon_cost R⟩

theorem admissible_bddBelow (R : Type u) [Ring R] [Nontrivial R] :
    BddBelow {τ : ℝ | Arithmetic.AdmissibleExponent R τ} :=
  ⟨2, fun _ => Arithmetic.admissibleExponent_two_le⟩

theorem omega_lower (R : Type u) [Ring R] [Nontrivial R] :
    (2 : ℝ) ≤ Arithmetic.omega R :=
  le_csInf (admissible_nonempty R) fun _ => Arithmetic.admissibleExponent_two_le

theorem omega_bound (R : Type u) [Ring R] :
    Arithmetic.omega R ≤ (9 : ℝ) / 4 := by
  cases subsingleton_or_nontrivial R
  · have hadm (τ : ℝ) : Arithmetic.AdmissibleExponent R τ := fun ε _ =>
      ⟨1, zero_lt_one, fun n _ => ⟨⟨1, .step .nil (.constant 0), fun _ _ => 0⟩,
        fun _ _ => Subsingleton.elim _ _, by
          simpa [Arithmetic.MatrixAlgorithm.cost, Arithmetic.Program.cost, Arithmetic.Gate.cost]
            using Real.rpow_nonneg (Nat.cast_nonneg n) (τ + ε)⟩⟩
    rw [Arithmetic.omega, Set.eq_univ_of_forall (s := {τ | Arithmetic.AdmissibleExponent R τ}) hadm, Real.sInf_univ]
    norm_num
  · exact csInf_le (admissible_bddBelow R) (epsilon_cost R)

theorem exact_coefficients (ε : ℝ) (hε : 0 < ε) :
    ∃ n r : ℕ, 2 ≤ n ∧ (r : ℝ) ≤ (n : ℝ) ^ ((9 : ℝ) / 4 + ε) ∧
      ∃ (a : Fin r → (Fin n × Fin n) → ℤ)
        (b : Fin r → (Fin n × Fin n) → ℤ)
        (c : Fin r → (Fin n × Fin n) → ℤ),
        ∀ x y z : Fin n × Fin n,
          (if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0 : ℤ) =
            ∑ i, a i x * b i y * c i z :=
  exists_int_scheme_nine_quarters hε

end ComparatorChecks
