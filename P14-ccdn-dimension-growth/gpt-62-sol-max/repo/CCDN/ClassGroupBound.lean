/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.TwoTorsion
import CCDN.ClassGroup.BalancedGenerator
import CCDN.ClassGroup.DiscriminantPrimeIdealCover
import CCDN.ClassGroup.NoIndexTwoClassGroupBound
import CCDN.ClassGroup.QuadraticClassGroupDescent
import CCDN.ClassGroup.QuadraticClassGroupNumerics

/-! CCDN Theorem 6 for the two-torsion subgroup of the ideal class
group. Constants are uniform over all number fields of the given degree.
Odd degrees have no logarithm; even degrees have exactly one logarithm.
The quadratic descent, exceptional subfields, lattice and curve counts
used by the proof are all proved in the imported modules. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField
universe u

/-- The parity-sensitive bound is also valid in degree two, which starts the descent. -/
private theorem classGroup_two_torsion_bound_from_two (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K : Type u) [Field K] [NumberField K], Module.finrank ℚ K = n →
        (classGroupTwoTorsionCard K : ℝ) ≤
          C * |(discr K : ℝ)| ^ (1 / 2 - 1 / (2 * (n : ℝ))) *
            (Real.log |(discr K : ℝ)|) ^ (1 - n % 2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hodd : Odd n
    · refine ⟨max 1 (oddDegreeClassGroupConstant n), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
      intro K _ _ hdeg
      rw [Nat.odd_iff.mp hodd, Nat.sub_self, pow_zero, mul_one]
      have hh := odd_degree_classGroup_two_torsion_bound K (by omega) (hdeg ▸ hodd)
      rw [hdeg] at hh
      exact hh.trans (by gcongr; exact le_max_right _ _)
    simp only [Nat.not_odd_iff.mp hodd, Nat.sub_zero, pow_one]
    by_cases htwo : n = 2
    · subst n
      obtain ⟨C, hC, hbound⟩ := quadratic_class_group_base_numeric
      refine ⟨C, hC, fun K _ _ hdeg => ?_⟩
      have hb := hbound (discr K).natAbs (numberField_discriminant_natAbs_pos K)
      rw [numberField_discriminant_natAbs_cast] at hb
      have hh := Nat.cast_le (α := ℝ) |>.mpr (quadratic_field_classGroupTwoTorsionCard_le K hdeg)
      push_cast at hh
      apply (hh.trans hb).trans
      have h : (1 / 2 - 1 / (2 * (↑(2 : ℕ) : ℝ))) = 1 / 4 := by norm_num
      rw [h]
      exact le_mul_of_one_le_right (by positivity) (one_le_log_abs_discr K (by omega))
    let m := n / 2
    have heven := Nat.not_odd_iff.mp hodd
    have hm : 2 ≤ m := by omega
    have hen : 2 * m = n := by omega
    obtain ⟨C, hC, hbase⟩ := ih m (by omega) hm
    obtain ⟨A, hA, hstep⟩ := quadratic_class_group_numeric_descent m hm C hC
    refine ⟨max A (noIndexTwoClassGroupConstant n), hA.trans_le (le_max_left _ _), ?_⟩
    intro K _ _ hdeg
    have hlog := one_le_log_abs_discr K (by omega)
    by_cases hno : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2
    · have hh := no_index_two_classGroup_two_torsion_bound K (by omega) hno
      rw [hdeg] at hh
      exact hh.trans (by gcongr; linarith [le_max_right A (noIndexTwoClassGroupConstant n)])
    push Not at hno
    obtain ⟨L, hL⟩ := hno
    have hLd : Module.finrank ℚ L = m := by
      have ht := Module.finrank_mul_finrank ℚ L K
      rw [hL, hdeg] at ht
      omega
    have hgenus := Nat.cast_le (α := ℝ) |>.mpr (quadratic_classGroupTwoTorsion_descent L K hL)
    rw [hdeg, hLd, ← hen] at hgenus
    push_cast at hgenus
    have hbaseL := hbase L hLd
    rw [← numberField_discriminant_natAbs_cast] at hbaseL
    have hl : 0 ≤ Real.log ((discr L).natAbs : ℝ) := by
      rw [numberField_discriminant_natAbs_cast]
      exact Real.log_nonneg (one_le_abs_discr L)
    have hbaseL' := hbaseL.trans (mul_le_mul_of_nonneg_left
      (show (Real.log ((discr L).natAbs : ℝ)) ^ (1 - m % 2) ≤
          Real.log ((discr L).natAbs : ℝ) + 1 from
        by rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h] at hl ⊢; linarith)
      (by positivity))
    have hh := hstep (discr K).natAbs (numberField_discriminant_natAbs_pos K)
      ((discr L).natAbs : ℝ) _ _ (by exact_mod_cast numberField_discriminant_natAbs_pos L)
      (by exact_mod_cast quadratic_absolute_discriminant_square_le K L hL) (by positivity)
      hbaseL' hgenus
    rw [hen, numberField_discriminant_natAbs_cast] at hh
    refine hh.trans ?_
    calc
      _ ≤ max A (noIndexTwoClassGroupConstant n) * _ := by gcongr; exact le_max_left _ _
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hlog

/-- The full class-group application, including the logarithmic exponent
specified by the parity of the field degree. -/
theorem classGroup_two_torsion_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K : Type u) [Field K] [NumberField K], Module.finrank ℚ K = n →
        (classGroupTwoTorsionCard K : ℝ) ≤
          C * |(discr K : ℝ)| ^ (1 / 2 - 1 / (2 * (n : ℝ))) *
            (Real.log |(discr K : ℝ)|) ^ (1 - n % 2) := classGroup_two_torsion_bound_from_two n (by omega)

end
end CCDN
