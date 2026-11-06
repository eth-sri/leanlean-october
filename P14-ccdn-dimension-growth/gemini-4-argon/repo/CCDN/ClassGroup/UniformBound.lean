/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.NoIndexTwoClassGroupBound
import CCDN.ClassGroup.BalancedGenerator
import CCDN.ClassGroup.DiscriminantPrimeIdealCover
import CCDN.ClassGroup.QuadraticClassGroupDescent
import CCDN.ClassGroup.QuadraticClassGroupNumerics

/-!
Uniform class-group bounds by strong induction on the field
degree. A quadratic subfield has smaller degree, and discriminant descent
leaves enough exponent saving to absorb the proved ramification factor.
The coefficient is chosen before the field.

Degree and discriminant facts used to assemble the class-group bound
by strong induction on the number-field degree.
-/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField
universe u

/-- The statement that every number field `K` of degree `n` satisfies
`h₂(K) ≤ C * |discr K| ^ (1 / 2 - 1 / (2 * n)) * (log |discr K| + 1)`. -/
def ClassGroupLogarithmicBound (n : ℕ) (C : ℝ) : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K], Module.finrank ℚ K = n →
    (classGroupTwoTorsionCard K : ℝ) ≤
      C * ((discr K).natAbs : ℝ) ^ (1 / 2 - 1 / (2 * (n : ℝ))) *
        (Real.log ((discr K).natAbs : ℝ) + 1)

/-- For every `n ≥ 2` there is a constant `C > 0` such that every number field `K` of degree `n`
satisfies `h₂(K) ≤ C * |discr K| ^ (1 / 2 - 1 / (2 * n)) * (log |discr K| + 1)`. -/
theorem classGroup_uniform_logarithmic_bound (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ClassGroupLogarithmicBound.{u} n C := by
  classical
  have hlog1 (K : Type u) [Field K] [NumberField K] :
      1 ≤ Real.log ((discr K).natAbs : ℝ) + 1 := by
    rw [numberField_discriminant_natAbs_cast]
    linarith [Real.log_nonneg (one_le_abs_discr K)]
  have hno2 (K : Type u) [Field K] [NumberField K] (hnK : 2 ≤ Module.finrank ℚ K)
      (hnoTwo : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2) :
      (classGroupTwoTorsionCard K : ℝ) ≤
        noIndexTwoClassGroupConstant (Module.finrank ℚ K) *
          ((discr K).natAbs : ℝ) ^ (1 / 2 - 1 / (2 * (Module.finrank ℚ K : ℝ))) *
            (Real.log ((discr K).natAbs : ℝ) + 1) := by
    rw [numberField_discriminant_natAbs_cast]
    exact (no_index_two_classGroup_two_torsion_bound K hnK hnoTwo).trans
      (mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg (noIndexTwoClassGroupConstant_pos _).le (Real.rpow_nonneg (abs_nonneg _) _)))
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn2 : n = 2
    · subst n
      obtain ⟨C, hC, hbound⟩ := quadratic_class_group_base_numeric
      refine ⟨C, hC, fun K _ _ hdeg => ?_⟩
      have hh : (classGroupTwoTorsionCard K : ℝ) ≤
          (2 : ℝ) ^ (4 * (discr K).natAbs.primeFactors.card + 2) :=
        mod_cast quadratic_field_classGroupTwoTorsionCard_le K hdeg
      have ht := (hh.trans (hbound (discr K).natAbs (numberField_discriminant_natAbs_pos K))).trans
        (le_mul_of_one_le_right (by positivity : 0 ≤ C * ((discr K).natAbs : ℝ) ^ (1 / 4 : ℝ))
          (hlog1 K))
      convert ht using 1; norm_num
    have hn3 : 3 ≤ n := by omega
    by_cases hm : 2 ≤ n / 2
    · obtain ⟨C, hC, hbase⟩ := ih (n / 2) (Nat.div_lt_self (by omega) (by omega)) hm
      obtain ⟨A, hA, hstep⟩ := quadratic_class_group_numeric_descent (n / 2) hm C hC
      let T := max A (noIndexTwoClassGroupConstant n)
      have hAT : A ≤ T := le_max_left _ _
      have hNT : noIndexTwoClassGroupConstant n ≤ T := le_max_right _ _
      refine ⟨T, hA.trans_le hAT, fun K _ _ hdeg => ?_⟩
      have hD : 1 ≤ (discr K).natAbs := numberField_discriminant_natAbs_pos K
      have hlog := hlog1 K
      by_cases hno : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2
      · have hh := hno2 K (by omega) hno
        rw [hdeg] at hh
        exact hh.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hNT (by positivity)) (by linarith))
      push Not at hno
      obtain ⟨L, hL⟩ := hno
      have ht := Module.finrank_mul_finrank ℚ L K
      rw [hL, hdeg] at ht
      have hLdeg : Module.finrank ℚ L = n / 2 := by omega
      have hnEq : n = 2 * (n / 2) := by omega
      have hLD : (1 : ℝ) ≤ ((discr L).natAbs : ℝ) := mod_cast numberField_discriminant_natAbs_pos L
      have hdisc : (((discr L).natAbs : ℝ) ^ 2) ≤ ((discr K).natAbs : ℝ) :=
        mod_cast quadratic_absolute_discriminant_square_le K L hL
      have hgenus : (classGroupTwoTorsionCard K : ℝ) ≤
          ((classGroupTwoTorsionCard L : ℝ) *
            (2 : ℝ) ^ ((2 * (n / 2)) * (discr K).natAbs.primeFactors.card + n / 2)) ^ 2 := by
        have hh := quadratic_classGroupTwoTorsion_descent L K hL
        rw [hdeg, hLdeg] at hh
        nth_rw 1 [hnEq] at hh
        exact_mod_cast hh
      have hh' : (classGroupTwoTorsionCard K : ℝ) ≤
          A * ((discr K).natAbs : ℝ) ^ (1 / 2 - 1 / (2 * (n : ℝ))) := by
        simpa only [← hnEq] using hstep (discr K).natAbs hD
          ((discr L).natAbs : ℝ) (classGroupTwoTorsionCard L : ℝ)
          (classGroupTwoTorsionCard K : ℝ) hLD hdisc (by positivity)
          (hbase L hLdeg) hgenus
      exact hh'.trans ((mul_le_mul_of_nonneg_right hAT (by positivity)).trans
        (le_mul_of_one_le_right (by positivity) hlog))
    · refine ⟨noIndexTwoClassGroupConstant n, noIndexTwoClassGroupConstant_pos n, fun K _ _ hdeg => ?_⟩
      have hno : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2 := fun L hL => by
        have ht := Module.finrank_mul_finrank ℚ L K
        rw [hL, hdeg] at ht; omega
      simpa only [hdeg] using hno2 K (by omega) hno

end
end CCDN
