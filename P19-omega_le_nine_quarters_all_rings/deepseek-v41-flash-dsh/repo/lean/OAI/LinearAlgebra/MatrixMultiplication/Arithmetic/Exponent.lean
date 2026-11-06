module

public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.NaiveAlgorithm
public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.LowerBound
public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Padding

public section

@[expose] section

namespace OAI

/-! Division-free arithmetic programs over a ring and their operation counts. -/


namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Ring F] [Nontrivial F]

theorem omega_two_le : 2 ≤ omega F :=
  le_csInf admissibleExponent_nonempty (fun _ hτ => admissibleExponent_two_le hτ)

theorem rectangularAdmissibleExponent_of_uniform_costs {k τ C : ℝ} (hC : 0 < C)
    (hbound : ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n (innerSize n k) n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ τ) :
    RectangularAdmissibleExponent F k τ := by
  intro ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (le_add_of_nonneg_right hε.le)

theorem rectangularAdmissibleExponent_naive (k : ℝ) :
    RectangularAdmissibleExponent F k (2 + max k 0) := by
  apply rectangularAdmissibleExponent_of_uniform_costs (C := 4) (by norm_num)
  intro n hn
  refine ⟨naiveAlgorithm n (innerSize n k) n,
    naiveAlgorithm_correct n (innerSize n k) n, ?_⟩
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hinner : (innerSize n k : ℝ) ≤ 2 * (n : ℝ) ^ max k 0 :=
    (Nat.cast_le.mpr (innerSize_mono hn (le_max_left k 0))).trans
      (innerSize_cast_le hn (le_max_right k 0))
  rw [naiveAlgorithm_cost]
  push_cast
  calc
    2 * (n : ℝ) * innerSize n k * n = 2 * (n : ℝ) ^ 2 * innerSize n k := by ring
    _ ≤ 2 * (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ max k 0) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 4 * (n : ℝ) ^ (2 + max k 0) := by
      rw [Real.rpow_add hnpos]
      norm_num
      ring

theorem rectangularAdmissibleExponent_nonempty (k : ℝ) :
    Set.Nonempty {τ : ℝ | RectangularAdmissibleExponent F k τ} :=
  ⟨2 + max k 0, rectangularAdmissibleExponent_naive k⟩

theorem rectangularOmega_two_le (k : ℝ) : 2 ≤ rectangularOmega F k :=
  le_csInf (rectangularAdmissibleExponent_nonempty k)
    (fun _ hτ => rectangularAdmissibleExponent_two_le hτ)

@[simp] theorem rectangularOmega_zero : rectangularOmega F 0 = 2 := by
  apply le_antisymm _ (rectangularOmega_two_le 0)
  apply rectangularOmega_le_of_admissibleExponent
  simpa using (rectangularAdmissibleExponent_naive (F := F) 0)

end MatrixMultiplication.Arithmetic


end OAI
