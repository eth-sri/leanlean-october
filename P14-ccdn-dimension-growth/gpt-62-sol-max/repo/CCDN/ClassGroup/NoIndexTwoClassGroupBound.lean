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
import CCDN.ClassGroup.OddDegreeClassGroupCounting
public import CCDN.ClassGroup.TwoTorsion

/-! The odd-degree and no-index-two bounds use the same translation-class lattice packing
at the balanced discriminant radius. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField

/-- The packing factor for the bounded translation classes, including the square-root term
from each norm curve at the balanced radius. -/
def classGroupPackingConstant (n : ℕ) : ℝ :=
  (numberFieldLatticeBoxConstant n ((n : ℝ) ^ 2) * (2 : ℝ) ^ n) * (3 * (9 : ℝ) ^ (n - 1))

/-- A coefficient depending only on the field degree. -/
def oddDegreeClassGroupConstant (n : ℕ) : ℝ :=
  (12 * affineHypersurfaceAuxiliaryConstant 0 * (n : ℝ) ^ 4) * classGroupPackingConstant n

/-- The constant for fields without an intermediate field of index two. -/
def noIndexTwoClassGroupConstant (n : ℕ) : ℝ :=
  noIndexTwoCurveContributionConstant n * classGroupPackingConstant n * (Real.log 9 + 2) +
    smallSubfieldIntegerCountConstant n * (9 : ℝ) ^ ((n : ℝ) / 4)

private lemma balanced_radius_log_le {D : ℝ} (hD : 0 < D) (hlog : 1 ≤ Real.log D)
    {n : ℕ} (hn : 0 < n) :
    Real.log (9 * D ^ (1 / (n : ℝ))) + 1 ≤
      (Real.log 9 + 2) * Real.log D := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 := zero_lt_one.trans_le hn1
  have hinv : 1 / (n : ℝ) ≤ 1 := (div_le_one hn0).mpr hn1
  have hl9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  rw [Real.log_mul (by norm_num : (9 : ℝ) ≠ 0) (Real.rpow_pos_of_pos hD _).ne',
    Real.log_rpow hD]
  nlinarith

variable (K : Type*) [Field K] [NumberField K]

local notation "nK" => Module.finrank ℚ K
local notation "D" => |(discr K : ℝ)|
local notation "B" => 9 * D ^ (1 / (nK : ℝ))
local notation "α" => (1 / 2 - 1 / (2 * (nK : ℝ)))

private lemma balanced_radius_one_le : 1 ≤ B := by
  linarith [Real.one_le_rpow (one_le_abs_discr K) (by positivity : 0 ≤ 1 / (nK : ℝ))]

private lemma balanced_translation_classes_count (hn : 2 ≤ nK) :
    ((boundedSquareNormTranslationClasses K B).card : ℝ) * Real.sqrt B ≤
      classGroupPackingConstant nK * D ^ α := by
  obtain ⟨b, hb, hnorm⟩ := exists_numberField_short_basis K hn
  have hr : 1 ≤ D ^ (1 / (nK : ℝ)) := Real.one_le_rpow (one_le_abs_discr K) (by positivity)
  have hc := boundedSquareNormTranslationClasses_count_of_relative_short_basis K b hb
    (balanced_radius_one_le K) (by positivity : 0 ≤ (nK : ℝ) ^ 2)
    (fun i => (hnorm i).trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity)))
  exact classGroup_discriminant_bound_of_balanced_radius (zero_lt_one.trans_le (one_le_abs_discr K))
    (by omega) (by linarith [mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg B)])

private lemma classGroupTwoTorsionCard_real_le :
    (classGroupTwoTorsionCard K : ℝ) ≤ (boundedSquareNormIntegers K B).ncard := by
  exact_mod_cast classGroupTwoTorsionCard_le_boundedSquareNormIntegers K

/-- The log-free odd-degree bound. -/
theorem odd_degree_classGroup_two_torsion_bound (hn : 2 ≤ nK) (hodd : Odd nK) :
    (classGroupTwoTorsionCard K : ℝ) ≤ oddDegreeClassGroupConstant nK * D ^ α := by
  have hcurves := boundedSquareNormIntegers_odd_count K hn hodd (balanced_radius_one_le K)
  have hA := affineHypersurfaceAuxiliaryConstant_pos 0
  have hp := mul_le_mul_of_nonneg_left (balanced_translation_classes_count K hn)
    (show 0 ≤ 12 * affineHypersurfaceAuxiliaryConstant 0 * (nK : ℝ) ^ 4 by positivity)
  unfold oddDegreeClassGroupConstant
  linarith [classGroupTwoTorsionCard_real_le K]

/-- With no index-two intermediate field, ordinary norm curves give the logarithmic main term;
small-subfield exceptions contribute at most a fourth root of the discriminant. -/
theorem no_index_two_classGroup_two_torsion_bound (hn : 2 ≤ nK)
    (hnoTwo : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2) :
    (classGroupTwoTorsionCard K : ℝ) ≤ noIndexTwoClassGroupConstant nK * D ^ α * Real.log D := by
  let P := noIndexTwoCurveContributionConstant nK
  let E := smallSubfieldIntegerCountConstant nK * (9 : ℝ) ^ ((nK : ℝ) / 4)
  have hD := one_le_abs_discr K
  have hlog := one_le_log_abs_discr K hn
  have hP : 0 ≤ P := noIndexTwoCurveContributionConstant_nonneg nK
  have hE : 0 ≤ E := mul_nonneg (smallSubfieldIntegerCountConstant_pos nK).le (by positivity)
  have hR := balanced_radius_one_le K
  have hS := boundedSquareNormIntegers_no_index_two_count K hnoTwo hn hR
  have hC := numberFieldLatticeBoxConstant_nonneg nK (show 0 ≤ (nK : ℝ) ^ 2 by positivity)
  have hboxes := balanced_translation_classes_count K hn
  have hb := balanced_radius_log_le (zero_lt_one.trans_le hD) hlog (by omega : 0 < nK)
  have hmain := mul_le_mul (mul_le_mul_of_nonneg_left hboxes hP) hb
    (add_nonneg (Real.log_nonneg hR) zero_le_one) (by unfold classGroupPackingConstant; positivity)
  have ha : (1 / 4 : ℝ) ≤ α := by
    have hnR : (2 : ℝ) ≤ nK := by exact_mod_cast hn
    linarith [one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
      (show (4 : ℝ) ≤ 2 * nK by linarith)]
  have hexc : ((boundedSmallSubfieldIntegers K B).ncard : ℝ) ≤ E * D ^ α * Real.log D :=
    (boundedSmallSubfieldIntegers_balanced_count K hD).trans
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hD ha) hE).trans
        (le_mul_of_one_le_right (by positivity) hlog))
  unfold noIndexTwoClassGroupConstant
  dsimp only [P, E] at *
  linarith [classGroupTwoTorsionCard_real_le K]

end
end CCDN
