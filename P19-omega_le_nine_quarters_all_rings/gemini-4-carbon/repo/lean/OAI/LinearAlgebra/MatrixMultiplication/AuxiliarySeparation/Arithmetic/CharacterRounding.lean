module

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.ExponentComparison
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Basic
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankExponent
public import Mathlib.Algebra.Order.Floor.Ring

public section

@[expose] section

namespace OAI

/-!
# Integer rounding in the detecting-character argument

The character used at a matrix size may depend on that size. A uniform bound
on all those characters is enough: the loss of one in rounding their target
values cannot change a positive power exponent. The character-existence and
character-growth assumptions remain explicit in the final implications.
-/

namespace MatrixMultiplication.AuxiliarySeparation

variable {K : Type*} [CommSemiring K]

open MatrixMultiplication.Foundation

/-- Rounding strictly down works at integers too: use `ceil x - 1`. -/
theorem exists_nat_sub_one_le_lt {x : ℝ} (hx : 0 < x) :
    ∃ k : ℕ, x - 1 ≤ (k : ℝ) ∧ (k : ℝ) < x := by
  have hc : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr hx
  refine ⟨⌈x⌉₊ - 1, ?_, ?_⟩
  · rw [Nat.cast_sub hc]
    norm_num only [Nat.cast_one]
    linarith [Nat.le_ceil x]
  · exact ((Nat.ceil_eq_iff (by omega : ⌈x⌉₊ ≠ 0)).1 rfl).1

/-- An additive loss of one does not affect a comparison to a nonnegative
power exponent. No sign assumption on the exponent on the left is needed. -/
theorem rpow_exponent_le_of_nat_sub_one_bound {ν τ : ℝ} (hτ : 0 ≤ τ)
    (hbound : ∀ d : ℕ, 2 ≤ d → (d : ℝ) ^ ν - 1 ≤ (d : ℝ) ^ τ) :
    ν ≤ τ := by
  apply rpow_exponent_le_of_nat_bound (C := 2)
  intro d hd
  by_cases hd2 : 2 ≤ d
  · have h := hbound d hd2
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hpow : 1 ≤ (d : ℝ) ^ τ := Real.one_le_rpow hdreal hτ
    linarith
  · have hd1 : d = 1 := by omega
    simp [hd1]

/-- The integer witnesses in the final rounding argument can vary with `d`. -/
theorem exponent_le_of_integer_rounding {ν τ : ℝ} (hτ : 0 ≤ τ)
    (hround : ∀ d : ℕ, 2 ≤ d →
      ∃ k : ℕ, (d : ℝ) ^ ν - 1 ≤ k ∧ (k : ℝ) ≤ (d : ℝ) ^ τ) :
    ν ≤ τ := by
  apply rpow_exponent_le_of_nat_sub_one_bound hτ
  intro d hd
  obtain ⟨k, hk, hk'⟩ := hround d hd
  exact hk.trans hk'

/-- Explicitly conditional passage from detecting characters to the exponent
bound. The detecting character is allowed to depend on both `d` and `k`. -/
theorem exponent_le_of_detecting_characters {ν τ : ℝ} (hτ : 0 ≤ τ)
    (detect : ∀ d : ℕ, 2 ≤ d → ∀ k : ℕ, (k : ℝ) < (d : ℝ) ^ ν →
      ∃ χ : (Character K), (k : ℝ) ≤ χ.value ((matrixMultiplicationTensor (K := K)) d d d))
    (bound : ∀ χ : (Character K), ∀ d : ℕ, 2 ≤ d →
      χ.value ((matrixMultiplicationTensor (K := K)) d d d) ≤ (d : ℝ) ^ τ) :
    ν ≤ τ := by
  apply exponent_le_of_integer_rounding hτ
  intro d hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨k, hk, hk'⟩ :=
    exists_nat_sub_one_le_lt (Real.rpow_pos_of_pos hdpos ν)
  obtain ⟨χ, hχ⟩ := detect d hd k hk'
  exact ⟨k, hk, hχ.trans (bound χ d hd)⟩

/-- The paper's final `ν ≤ 9/4` implication, with its two substantive character
inputs visible rather than incorporated into the definition of `ν`. -/
theorem exactRankExponent_le_nine_quarters_of_characters [Nontrivial K]
    (detect : ∀ d : ℕ, 2 ≤ d → ∀ k : ℕ,
      (k : ℝ) < (d : ℝ) ^ (exactRankExponent K) →
      ∃ χ : (Character K), (k : ℝ) ≤ χ.value ((matrixMultiplicationTensor (K := K)) d d d))
    (bound : ∀ χ : (Character K), ∀ d : ℕ, 2 ≤ d →
      χ.value ((matrixMultiplicationTensor (K := K)) d d d) ≤ (d : ℝ) ^ (9 / 4 : ℝ)) :
    (exactRankExponent K) ≤ 9 / 4 :=
  exponent_le_of_detecting_characters (by norm_num) detect bound

end MatrixMultiplication.AuxiliarySeparation

end OAI
