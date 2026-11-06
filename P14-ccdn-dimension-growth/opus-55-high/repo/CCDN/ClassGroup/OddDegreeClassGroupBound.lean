/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.AffineHypersurfaceAuxiliary
import CCDN.ClassGroup.NumberFieldLatticeBox
import CCDN.ClassGroup.BalancedGenerator
import CCDN.ClassGroup.DiscriminantNumerics
import CCDN.ClassGroup.NumberFieldShortBasis
import CCDN.ClassGroup.OddDegreeClassGroupCounting

/-! The odd-degree branch of CCDN Theorem 6 for the ideal-class
group, via the lattice, bounded representatives, translation classes, and
signed norm curves of the imported files. -/

namespace CCDN
noncomputable section
open NumberField NumberField.InfinitePlace

/-- A coefficient depending only on the field degree. -/
def oddDegreeClassGroupConstant (n : ℕ) : ℝ :=
  (12 * affineHypersurfaceAuxiliaryConstant 0 * (n : ℝ) ^ 4) *
    (numberFieldLatticeBoxConstant n ((n : ℝ) ^ 3) * (2 : ℝ) ^ n) *
    (3 * (9 : ℝ) ^ (n - 1))

variable (K : Type*) [Field K] [NumberField K]

/-- The log-free odd-degree bound. -/
theorem odd_degree_classGroup_two_torsion_bound
    (hn : 2 ≤ Module.finrank ℚ K) (hodd : Odd (Module.finrank ℚ K)) :
    (classGroupTwoTorsionCard K : ℝ) ≤
      oddDegreeClassGroupConstant (Module.finrank ℚ K) *
        |(discr K : ℝ)| ^
          (1 / 2 - 1 / (2 * (Module.finrank ℚ K : ℝ))) := by
  classical
  have hD1 := one_le_abs_discr K
  have hD := zero_lt_one.trans_le hD1
  let B := 9 * |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ))
  have hroot : 1 ≤ |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) :=
    Real.one_le_rpow hD1 (by positivity)
  have hB : 1 ≤ B := by grind
  obtain ⟨b, hb, hnorm⟩ := exists_numberField_short_basis K hn
  have hnormB (i) : ‖b i‖ ≤ (Module.finrank ℚ K : ℝ) ^ 3 * B := by
    apply (hnorm i).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    grind
  have hbound := boundedSquareNormIntegers_odd_count_of_relative_short_basis K b hb
    hn hodd hB (by simp_all) hnormB
  have hcard : (classGroupTwoTorsionCard K : ℝ) ≤
      (boundedSquareNormIntegers K B).ncard := by
    dsimp [B]
    exact_mod_cast (classGroupTwoTorsionCard_le_boundedSquareNormIntegers K)
  have hh := (mul_le_mul_of_nonneg_right hcard
    (Real.sqrt_nonneg |(discr K : ℝ)|)).trans hbound
  have ht := classGroup_discriminant_bound_of_balanced_radius hD
    (by grind) hh
  exact ht

