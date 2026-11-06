/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.NoIndexTwoClassGroupCounting
public import CCDN.ClassGroup.NumberFieldLatticeBox
import CCDN.ClassGroup.BalancedGenerator
import CCDN.ClassGroup.DiscriminantNumerics
import CCDN.ClassGroup.NumberFieldShortBasis

/-!
The logarithmic branch of CCDN Theorem 6 for number fields with no
index-two intermediate field. All ideal-class representatives, curves,
lattice points and exceptional subfields are constructed and counted.

Uniform finite-radius counts for the ring of integers and its
integer-translation classes. The required short basis is constructed,
and every coefficient depends only on the degree.
-/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField

/-- The degree-dependent constant in the two-torsion class-group bound for number fields of degree
`n` without an intermediate field of index two. -/
def noIndexTwoClassGroupConstant (n : ℕ) : ℝ :=
  (noIndexTwoCurveContributionConstant n *
    (numberFieldLatticeBoxConstant n ((n : ℝ) ^ 3) * (2 : ℝ) ^ n) *
      (3 * (9 : ℝ) ^ (n - 1))) * (Real.log 9 + 2) +
    smallSubfieldIntegerCountConstant n * (9 : ℝ) ^ ((n : ℝ) / 4)

/-- The constant `noIndexTwoClassGroupConstant n` is positive. -/
lemma noIndexTwoClassGroupConstant_pos (n : ℕ) :
    0 < noIndexTwoClassGroupConstant n := by
  have hc := noIndexTwoCurveContributionConstant_nonneg n
  have hb := numberFieldLatticeBoxConstant_nonneg n (by positivity : 0 ≤ (n : ℝ) ^ 3)
  have he := smallSubfieldIntegerCountConstant_pos n
  have hl : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  unfold noIndexTwoClassGroupConstant
  positivity

variable (K : Type*) [Field K] [NumberField K]

/-- For a number field `K` of degree `n ≥ 2` with no intermediate field `L` of index `[K : L] = 2`,
the two-torsion subgroup of the class group has order at most
`C(n) * |discr K| ^ (1 / 2 - 1 / (2 * n)) * log |discr K|`. -/
theorem no_index_two_classGroup_two_torsion_bound
    (hn : 2 ≤ Module.finrank ℚ K)
    (hnoTwo : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2) :
    (classGroupTwoTorsionCard K : ℝ) ≤
      noIndexTwoClassGroupConstant (Module.finrank ℚ K) *
        |(discr K : ℝ)| ^
          (1 / 2 - 1 / (2 * (Module.finrank ℚ K : ℝ))) *
            Real.log |(discr K : ℝ)| := by
  let n := Module.finrank ℚ K
  let D := |(discr K : ℝ)|
  let B := 9 * D ^ (1 / (n : ℝ))
  let P := noIndexTwoCurveContributionConstant n
  let A := numberFieldLatticeBoxConstant n ((n : ℝ) ^ 3) * (2 : ℝ) ^ n
  let E := smallSubfieldIntegerCountConstant n * (9 : ℝ) ^ ((n : ℝ) / 4)
  let a := 1 / 2 - 1 / (2 * (n : ℝ))
  have hnpos : 0 < n := by dsimp [n]; omega
  have hnR : (2 : ℝ) ≤ n := mod_cast hn
  have hD3 : 3 ≤ D := three_le_abs_discr K hn
  have hD1 : 1 ≤ D := by linarith
  have hD : 0 < D := by linarith
  have hlog : 1 ≤ Real.log D := one_le_log_abs_discr K hn
  have hroot : 1 ≤ D ^ (1 / (n : ℝ)) := Real.one_le_rpow hD1 (by positivity)
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hBroot : D ^ (1 / (n : ℝ)) ≤ B := by dsimp [B]; linarith
  have hP : 0 ≤ P := noIndexTwoCurveContributionConstant_nonneg n
  have hA : 0 ≤ A := mul_nonneg
    (numberFieldLatticeBoxConstant_nonneg n (by positivity)) (by positivity)
  have hE : 0 ≤ E := mul_nonneg (smallSubfieldIntegerCountConstant_pos n).le (by positivity)
  have hlogB : 0 ≤ Real.log B + 1 := by linarith [Real.log_nonneg hB]
  have hS := boundedSquareNormIntegers_no_index_two_count K hnoTwo hn hB
  obtain ⟨b, hb, hnorm⟩ := exists_numberField_short_basis K hn
  have hQ := boundedSquareNormTranslationClasses_count_of_relative_short_basis K b hb hB
    (by positivity : 0 ≤ (n : ℝ) ^ 3)
    fun i => (hnorm i).trans (mul_le_mul_of_nonneg_left hBroot (by positivity))
  have hmain : P * (boundedSquareNormTranslationClasses K B).card * Real.sqrt B *
      (Real.log B + 1) ≤ (P * A * (3 * (9 : ℝ) ^ (n - 1))) * D ^ a * (Real.log B + 1) := by
    have hm := mul_le_mul_of_nonneg_left hQ (mul_nonneg (mul_nonneg hP (Real.sqrt_nonneg B)) hlogB)
    have hpre : (P * (boundedSquareNormTranslationClasses K B).card * Real.sqrt B *
        (Real.log B + 1)) * Real.sqrt D ≤ (P * A * (Real.log B + 1)) * (B ^ (n - 1) * Real.sqrt B) := by
      convert hm using 1 <;> ring
    exact (classGroup_discriminant_bound_of_balanced_radius hD hnpos hpre).trans_eq (by ring)
  have hbal : Real.log B + 1 ≤ (Real.log 9 + 2) * Real.log D := by
    have hinv : 1 / (n : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have hl9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
    dsimp [B]
    rw [Real.log_mul (by norm_num : (9 : ℝ) ≠ 0) (Real.rpow_pos_of_pos hD _).ne', Real.log_rpow hD]
    nlinarith
  have hmain' : P * (boundedSquareNormTranslationClasses K B).card * Real.sqrt B *
      (Real.log B + 1) ≤
      (P * A * (3 * (9 : ℝ) ^ (n - 1)) * (Real.log 9 + 2)) * D ^ a * Real.log D :=
    hmain.trans ((mul_le_mul_of_nonneg_left hbal
      (show 0 ≤ (P * A * (3 * (9 : ℝ) ^ (n - 1))) * D ^ a by positivity)).trans_eq (by ring))
  have hexc : ((boundedSmallSubfieldIntegers K B).ncard : ℝ) ≤ E * D ^ a * Real.log D := by
    have ha : (1 / 4 : ℝ) ≤ a := by
      have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) (show (4 : ℝ) ≤ 2 * n by linarith)
      dsimp [a]; linarith
    exact ((boundedSmallSubfieldIntegers_balanced_count K hD1).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hD1 ha) hE)).trans
      (le_mul_of_one_le_right (by positivity) hlog)
  have hcard : (classGroupTwoTorsionCard K : ℝ) ≤ (boundedSquareNormIntegers K B).ncard := by
    dsimp only [B, D, n]; exact_mod_cast classGroupTwoTorsionCard_le_boundedSquareNormIntegers K
  exact ((hcard.trans hS).trans (add_le_add hexc hmain')).trans_eq
    (by unfold noIndexTwoClassGroupConstant; dsimp [E, P, A, n, D, a]; ring)

end
end CCDN
