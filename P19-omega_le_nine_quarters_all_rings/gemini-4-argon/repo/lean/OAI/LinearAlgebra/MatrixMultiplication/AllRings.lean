module

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Existence
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.Inequalities
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Integral.FiniteSeparation
public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Growth

public section

@[expose] section

namespace OAI.MatrixMultiplication

universe u

namespace AuxiliarySeparation.Integral

theorem exactRankExponent_int_le_nine_quarters :
    exactRankExponent ℤ ≤ (9 : ℝ) / 4 := by
  apply exactRankExponent_le_nine_quarters_of_characters
  · intro d hd k hk
    exact exists_detecting_character hd hk
  · intro χ d hd
    rw [χ.value_matrixMultiplication (by omega)]
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ d by omega))
    apply χ.exponent_sum_le_nine_quarters_of_separation_and_convolution
    · intro ψ M X Y Z _ _ _ hM B
      exact finiteSeparation_bound_int ψ hM B
    · intro ψ a b
      exact ψ.value_convolution_le_int a b

end AuxiliarySeparation.Integral

theorem admissibleExponent_nine_quarters_all_rings (R : Type u) [Ring R] :
    Arithmetic.AdmissibleExponent R ((9 : ℝ) / 4) :=
  Arithmetic.admissibleExponent_of_int_rank_bounds (by norm_num) fun ε hε => by
    obtain ⟨n, r, hn, hrank, hr⟩ :=
      AuxiliarySeparation.exists_rankAtMost_of_exponent_slack (K := ℤ) hε
    exact ⟨n, r, hn, hrank, hr.trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (by omega : 1 ≤ n))
      (by linarith [AuxiliarySeparation.Integral.exactRankExponent_int_le_nine_quarters]))⟩

theorem omega_le_nine_quarters_all_rings (R : Type u) [Ring R] :
    Arithmetic.omega R ≤ (9 : ℝ) / 4 := by
  cases subsingleton_or_nontrivial R
  · have huniv : {τ : ℝ | Arithmetic.AdmissibleExponent R τ} = Set.univ :=
      Set.eq_univ_of_forall fun τ ε _ => ⟨1, zero_lt_one, fun n _ =>
        ⟨⟨1, .step .nil (.constant 0), fun _ _ => 0⟩, fun _ _ => Subsingleton.elim _ _,
          by simpa [Arithmetic.MatrixAlgorithm.cost, Arithmetic.Program.cost,
            Arithmetic.Gate.cost] using Real.rpow_nonneg (Nat.cast_nonneg n) (τ + ε)⟩⟩
    rw [Arithmetic.omega, huniv, Real.sInf_univ]
    norm_num
  · exact Arithmetic.omega_le_of_admissibleExponent (admissibleExponent_nine_quarters_all_rings R)

theorem matrix_multiplication_cost_le_nine_quarters_all_rings
    (R : Type u) [Ring R] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : Arithmetic.MatrixAlgorithm R n n n,
        P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ ((9 : ℝ) / 4 + ε) :=
  admissibleExponent_nine_quarters_all_rings R ε hε

end OAI.MatrixMultiplication
