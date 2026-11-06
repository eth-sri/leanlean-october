/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.ClassGroup.NoIndexTwoClassGroupBound
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

namespace CCDN
section
open NumberField

variable (K : Type*) [Field K] [NumberField K]

lemma one_le_log_discr_natAbs_add_one : 1 ≤ Real.log ((discr K).natAbs : ℝ) + 1 := by
  rw [numberField_discriminant_natAbs_cast]
  linarith [Real.log_nonneg (one_le_abs_discr K)]

theorem index_two_subfield_degree
    (hn : 3 ≤ Module.finrank ℚ K) (L : IntermediateField ℚ K)
    (hL : Module.finrank L K = 2) :
    Module.finrank ℚ L = Module.finrank ℚ K / 2 ∧
      2 ≤ Module.finrank ℚ L := by
  have ht := Module.finrank_mul_finrank ℚ L K
  rw [hL] at ht
  omega

theorem no_index_two_classGroup_log_one_bound
    (hn : 2 ≤ Module.finrank ℚ K)
    (hnoTwo : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2) :
    (classGroupTwoTorsionCard K : ℝ) ≤
      noIndexTwoClassGroupConstant (Module.finrank ℚ K) *
        ((discr K).natAbs : ℝ) ^
          (1 / 2 - 1 / (2 * (Module.finrank ℚ K : ℝ))) *
            (Real.log ((discr K).natAbs : ℝ) + 1) := by
  rw [numberField_discriminant_natAbs_cast]
  apply (show (classGroupTwoTorsionCard K : ℝ) ≤
        noIndexTwoClassGroupConstant (Module.finrank ℚ K) *
          |(discr K : ℝ)| ^
            (1 / 2 - 1 / (2 * (Module.finrank ℚ K : ℝ))) *
              Real.log |(discr K : ℝ)| by
      let n := Module.finrank ℚ K
      let D := |(discr K : ℝ)|
      let B := 9 * D ^ (1 / (n : ℝ))
      let P := noIndexTwoCurveContributionConstant n
      let A := numberFieldLatticeBoxConstant n (n ^ 3) * (2 : ℝ) ^ n
      let E := smallSubfieldIntegerCountConstant n * (9 : ℝ) ^ ((n : ℝ) / 4)
      let a := 1 / 2 - 1 / (2 * (n : ℝ))
      have hnpos : 0 < n := by grind
      have hnR : (2 : ℝ) ≤ n := mod_cast hn
      have hD3 := three_le_abs_discr K hn
      have hD1 : 1 ≤ D := by linarith
      have hD : 0 < D := by linarith
      have hlog := one_le_log_abs_discr K hn
      have hroot : 1 ≤ D ^ (1 / (n : ℝ)) := Real.one_le_rpow hD1 (by positivity)
      have hB : 1 ≤ B := by grind
      have hP := noIndexTwoCurveContributionConstant_nonneg n
      have hA : 0 ≤ A := mul_nonneg
        (numberFieldLatticeBoxConstant_nonneg n (by positivity)) (by positivity)
      have hE : 0 ≤ E := mul_nonneg (smallSubfieldIntegerCountConstant_pos n).le (by positivity)
      have hlogB : 0 ≤ Real.log B + 1 := by linarith [Real.log_nonneg hB]
      have hS := boundedSquareNormIntegers_no_index_two_count K hnoTwo hn hB
      have hQ : ((boundedSquareNormTranslationClasses K B).card : ℝ) * Real.sqrt |(discr K : ℝ)| ≤
          (numberFieldLatticeBoxConstant (Module.finrank ℚ K) ((Module.finrank ℚ K : ℝ) ^ 3) *
            (2 : ℝ) ^ Module.finrank ℚ K) * B ^ (Module.finrank ℚ K - 1) := by
        obtain ⟨b, hb, hnorm⟩ := exists_numberField_short_basis K hn
        apply boundedSquareNormTranslationClasses_count_of_relative_short_basis K b hb hB
          (by positivity)
        exact fun i ↦ (hnorm i).trans (mul_le_mul_of_nonneg_left (by grind) (by positivity))
      have hmain :
          P * (boundedSquareNormTranslationClasses K B).card * Real.sqrt B *
              (Real.log B + 1) ≤
            (P * A * (3 * (9 : ℝ) ^ (n - 1))) * D ^ a * (Real.log B + 1) := by
        have hm := mul_le_mul_of_nonneg_left hQ
          (mul_nonneg (mul_nonneg hP (Real.sqrt_nonneg B)) hlogB)
        have hpre :
            (P * (boundedSquareNormTranslationClasses K B).card * Real.sqrt B *
                (Real.log B + 1)) * Real.sqrt D ≤
              (P * A * (Real.log B + 1)) *
                (B ^ (n - 1) * Real.sqrt B) := by
          convert hm using 1 <;> ring
        have hh := classGroup_discriminant_bound_of_balanced_radius hD hnpos hpre
        convert hh using 1
        ring
      have hmain' :
          P * (boundedSquareNormTranslationClasses K B).card * Real.sqrt B *
              (Real.log B + 1) ≤
            (P * A * (3 * (9 : ℝ) ^ (n - 1)) * (Real.log 9 + 2)) *
              D ^ a * Real.log D := by
        apply hmain.trans
        have hh := mul_le_mul_of_nonneg_left (show Real.log (9 * D ^ (1 / (n : ℝ))) + 1 ≤
              (Real.log 9 + 2) * Real.log D by
            have hn1 : (1 : ℝ) ≤ n := mod_cast hnpos
            have hn0 := zero_lt_one.trans_le hn1
            have hinv := (div_le_one hn0).mpr hn1
            have hl9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
            rw [Real.log_mul (by norm_num : (9 : ℝ) ≠ 0) (Real.rpow_pos_of_pos hD _).ne',
              Real.log_rpow hD]
            nlinarith)
          (show 0 ≤ (P * A * (3 * (9 : ℝ) ^ (n - 1))) * D ^ a by positivity)
        convert hh using 1
        ring
      have hexc :
          ((boundedSmallSubfieldIntegers K B).ncard : ℝ) ≤ E * D ^ a * Real.log D := by
        have hh : ((boundedSmallSubfieldIntegers K
              (9 * D ^ (1 / (Module.finrank ℚ K : ℝ)))).ncard : ℝ) ≤
            (smallSubfieldIntegerCountConstant (Module.finrank ℚ K) *
              (9 : ℝ) ^ ((Module.finrank ℚ K : ℝ) / 4)) * D ^ (1 / 4 : ℝ) := by
          have hn : (0 : ℝ) < Module.finrank ℚ K := by
            exact_mod_cast (Module.finrank_pos)
          have hD0 := zero_lt_one.trans_le hD1
          have hB : 1 ≤ 9 * D ^ (1 / (Module.finrank ℚ K : ℝ)) := by
            have hh := Real.one_le_rpow hD1 (by positivity : 0 ≤ 1 / (Module.finrank ℚ K : ℝ))
            linarith
          have hh := boundedSmallSubfieldIntegers_count K hB
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 9) (Real.rpow_nonneg hD0.le _),
            ← Real.rpow_mul hD0.le] at hh
          have he : 1 / (Module.finrank ℚ K : ℝ) *
              ((Module.finrank ℚ K : ℝ) / 4) = 1 / 4 := by field_simp
          rw [he] at hh
          convert hh using 1
          ring
        have ha : (1 / 4 : ℝ) ≤ a := by
          have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
            (show (4 : ℝ) ≤ 2 * n by linarith)
          grind
        have hp := Real.rpow_le_rpow_of_exponent_le hD1 ha
        calc
          _ ≤ E * D ^ (1 / 4 : ℝ) := hh
          _ ≤ E * D ^ a := mul_le_mul_of_nonneg_left hp hE
          _ ≤ E * D ^ a * Real.log D := le_mul_of_one_le_right (by positivity) hlog
      have hcard : (classGroupTwoTorsionCard K : ℝ) ≤
          (boundedSquareNormIntegers K B).ncard := by
        dsimp [B, D, n]
        exact_mod_cast classGroupTwoTorsionCard_le_boundedSquareNormIntegers K
      calc
        _ ≤ _ := hcard.trans hS
        _ ≤ E * D ^ a * Real.log D +
            (P * A * (3 * (9 : ℝ) ^ (n - 1)) * (Real.log 9 + 2)) *
              D ^ a * Real.log D := add_le_add hexc hmain'
        _ = _ := by unfold noIndexTwoClassGroupConstant; dsimp [E, P, A, n, D, a]; ring).trans
  exact mul_le_mul_of_nonneg_left (by linarith : Real.log |(discr K : ℝ)| ≤
    Real.log |(discr K : ℝ)| + 1) (by
      exact mul_nonneg (noIndexTwoClassGroupConstant_pos _).le
        (Real.rpow_nonneg (abs_nonneg _) _))

end

section
open NumberField
universe u

variable (n : ℕ)

/-- The statement that every number field `K` of degree `n` satisfies
`h₂(K) ≤ C * |discr K| ^ (1 / 2 - 1 / (2 * n)) * (log |discr K| + 1)`. -/
def ClassGroupLogarithmicBound (C : ℝ) : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K], Module.finrank ℚ K = n →
    (classGroupTwoTorsionCard K : ℝ) ≤
      C * ((discr K).natAbs : ℝ) ^ (1 / 2 - 1 / (2 * (n : ℝ))) *
        (Real.log ((discr K).natAbs : ℝ) + 1)

/-- For every `n ≥ 2` there is a constant `C > 0` such that every number field `K` of degree `n`
satisfies `h₂(K) ≤ C * |discr K| ^ (1 / 2 - 1 / (2 * n)) * (log |discr K| + 1)`. -/
theorem classGroup_uniform_logarithmic_bound (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ClassGroupLogarithmicBound.{u} n C := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn2 : n = 2
    · subst n
      obtain ⟨C, hC, hbound⟩ : ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 1 ≤ D →
          (2 : ℝ) ^ (4 * D.primeFactors.card + 2) ≤ C * (D : ℝ) ^ (1 / 4 : ℝ) := by
        obtain ⟨C, hC, hbound⟩ := two_pow_primeFactors_subpower 4
          (by norm_num : (0 : ℝ) < 1 / 4)
        refine ⟨4 * C, by positivity, ?_⟩
        intro D hD
        rw [pow_add]
        norm_num
        nlinarith [hbound D hD]
      refine ⟨C, hC, ?_⟩
      intro K _ _ hdeg
      have hh : (classGroupTwoTorsionCard K : ℝ) ≤
          (2 : ℝ) ^ (4 * (discr K).natAbs.primeFactors.card + 2) := by
        exact_mod_cast quadratic_field_classGroupTwoTorsionCard_le K hdeg
      have hb := hh.trans (hbound (discr K).natAbs (numberField_discriminant_natAbs_pos K))
      have ht := hb.trans (le_mul_of_one_le_right
        (by grind)
        (one_le_log_discr_natAbs_add_one K))
      grind
    have hn3 : 3 ≤ n := by omega
    by_cases hm : 2 ≤ n / 2
    · obtain ⟨C, hC, hbase⟩ := ih (n / 2)
        (Nat.div_lt_self (by omega) (by omega)) hm
      obtain ⟨A, hA, hstep⟩ := quadratic_class_group_numeric_descent (n / 2) hm C hC
      let T := max A (noIndexTwoClassGroupConstant n)
      have hAT : A ≤ T := le_max_left _ _
      have hNT : noIndexTwoClassGroupConstant n ≤ T := le_max_right _ _
      refine ⟨T, hA.trans_le hAT, ?_⟩
      intro K _ _ hdeg
      have hD := numberField_discriminant_natAbs_pos K
      have hlog := one_le_log_discr_natAbs_add_one K
      by_cases hno : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2
      · have hh := no_index_two_classGroup_log_one_bound K (by omega) hno
        rw [hdeg] at hh
        apply hh.trans
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hNT (by positivity)) (by linarith)
      push Not at hno
      obtain ⟨L, hL⟩ := hno
      obtain ⟨hLdeg, -⟩ := index_two_subfield_degree K (by omega) L hL
      rw [hdeg] at hLdeg
      have hnEq : n = 2 * (n / 2) := by
        have ht := Module.finrank_mul_finrank ℚ L K
        grind
      have hLD : (1 : ℝ) ≤ ((discr L).natAbs : ℝ) := by
        exact_mod_cast numberField_discriminant_natAbs_pos L
      have hdisc : (((discr L).natAbs : ℝ) ^ 2) ≤ ((discr K).natAbs : ℝ) := by
        exact_mod_cast quadratic_absolute_discriminant_square_le K L hL
      have hgenus : (classGroupTwoTorsionCard K : ℝ) ≤
          ((classGroupTwoTorsionCard L : ℝ) *
            (2 : ℝ) ^ ((2 * (n / 2)) * (discr K).natAbs.primeFactors.card + n / 2)) ^ 2 := by
        have hh := quadratic_classGroupTwoTorsion_descent L K hL
        rw [hdeg, hLdeg] at hh
        nth_rw 1 [hnEq] at hh
        exact_mod_cast hh
      have hh := hstep (discr K).natAbs hD
        ((discr L).natAbs : ℝ) (classGroupTwoTorsionCard L : ℝ)
        (classGroupTwoTorsionCard K : ℝ) hLD hdisc (by positivity)
        (hbase L hLdeg) hgenus
      have hh' : (classGroupTwoTorsionCard K : ℝ) ≤
          A * ((discr K).natAbs : ℝ) ^ (1 / 2 - 1 / (2 * (n : ℝ))) := by
        simpa [← hnEq] using hh
      apply hh'.trans
      exact (mul_le_mul_of_nonneg_right hAT (by positivity)).trans
        (le_mul_of_one_le_right (by positivity) hlog)
    · refine ⟨noIndexTwoClassGroupConstant n, noIndexTwoClassGroupConstant_pos n, ?_⟩
      intro K _ _ hdeg
      have hno : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2 := by
        intro L hL
        obtain ⟨hLdeg, hmL⟩ := index_two_subfield_degree K (by omega) L hL
        grind
      simpa [hdeg] using no_index_two_classGroup_log_one_bound K (by omega) hno

