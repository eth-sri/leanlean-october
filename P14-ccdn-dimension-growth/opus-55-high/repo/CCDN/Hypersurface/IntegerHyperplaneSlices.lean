/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Height.Box
import Mathlib.Algebra.BigOperators.Fin

/-! Counting bounded integral points by the integer values of a
linear form. Deleting a coordinate with nonzero coefficient is injective
on each level and preserves the box radius. -/

namespace CCDN

section
variable {n : ℕ}

/-- The value `∑ a i * x i` of the integer linear form with coefficients `a` at the point `x`. -/
def integerLinearLevel (a x : IntPoint n) : ℤ := ∑ i, a i * x i

/-- The projection of an integer point in `n + 1` coordinates to `n` coordinates by deleting
coordinate `j`. -/
def deleteIntegerCoordinate (j : Fin (n + 1))
    (x : IntPoint (n + 1)) : IntPoint n := fun i => x (j.succAbove i)

end

section
variable {n : ℕ} (X : Set (RatPoint n)) (B : ℝ) (a : IntPoint n)

/-- The integral points of `X` of height at most `B` on the level set `∑ a i * x i = k` of the
integer linear form with coefficients `a`. -/
noncomputable def integerSlicePoints
    (k : ℤ) : Finset (IntPoint n) := by
  exact (integralPoints X B).filter fun x => integerLinearLevel a x = k

noncomputable def integerSliceLevels
    : Finset ℤ := by
  exact (integralPoints X B).image (integerLinearLevel a)

end

section
variable {n : ℕ} {H B : ℝ}

theorem integerLinearLevel_abs_le (a x : IntPoint n)
    (hH : 0 ≤ H) (ha : InBox a H)
    (hx : InBox x B) :
    |(integerLinearLevel a x : ℝ)| ≤ (n : ℝ) * H * B := by
  simp [integerLinearLevel, Int.cast_sum, Int.cast_mul]
  calc
    |∑ i, (a i : ℝ) * (x i : ℝ)| ≤ ∑ i, |(a i : ℝ) * (x i : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, H * B := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (ha i) (hx i) (abs_nonneg _) hH
    _ = _ := by simp [mul_assoc]

theorem integerSliceLevels_card_le (X : Set (RatPoint n))
    (a : IntPoint n) (hH : 0 ≤ H) (hB : 0 ≤ B)
    (ha : InBox a H) :
    ((integerSliceLevels X B a).card : ℝ) ≤ 2 * (n : ℝ) * H * B + 1 := by
  let R : ℝ := n * H * B
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hH) hB
  have hsub : integerSliceLevels X B a ⊆ Finset.Icc (-⌊R⌋) ⌊R⌋ := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    have hb := integerLinearLevel_abs_le a x hH ha (mem_integralPoints.mp hx).1
    have hpos :=
      Int.le_floor.mpr (le_trans (le_abs_self _) hb)
    have hneg : -integerLinearLevel a x ≤ ⌊R⌋ :=
      Int.le_floor.mpr (by grind)
    grind
  have hcard := Finset.card_le_card hsub
  have hfloor := Int.floor_nonneg.mpr hR
  have hcast : (((⌊R⌋ + 1 - -⌊R⌋).toNat : ℕ) : ℝ) =
      2 * (⌊R⌋ : ℝ) + 1 := by
    have he := Int.toNat_of_nonneg (show 0 ≤ ⌊R⌋ + 1 - -⌊R⌋ by omega)
    exact_mod_cast (show ((⌊R⌋ + 1 - -⌊R⌋).toNat : ℤ) = 2 * ⌊R⌋ + 1 by omega)
  rw [Int.card_Icc] at hcard
  have hr : ((integerSliceLevels X B a).card : ℝ) ≤
      (((⌊R⌋ + 1 - -⌊R⌋).toNat : ℕ) : ℝ) := mod_cast hcard
  rw [hcast] at hr
  calc
    _ ≤ 2 * R + 1 := by linarith [Int.floor_le R]
    _ = _ := by grind

end

theorem deleteIntegerCoordinate_injective_on_level {n : ℕ}
    (a : IntPoint (n + 1)) (j : Fin (n + 1)) (hj : a j ≠ 0)
    {x y : IntPoint (n + 1)}
    (hlevel : integerLinearLevel a x = integerLinearLevel a y)
    (hdelete : deleteIntegerCoordinate j x = deleteIntegerCoordinate j y) :
    x = y := by
  have hrest : ∑ i : Fin n, a (j.succAbove i) * x (j.succAbove i) =
      ∑ i : Fin n, a (j.succAbove i) * y (j.succAbove i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [show x (j.succAbove i) = y (j.succAbove i) from congrFun hdelete i]
  have hpivot : x j = y j := by
    unfold integerLinearLevel at hlevel
    rw [Fin.sum_univ_succAbove _ j, Fin.sum_univ_succAbove _ j] at hlevel
    simp_all
  funext i
  by_cases hi : i = j
  · grind
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
    exact congrFun hdelete k

variable {n : ℕ} (X : Set (RatPoint (n + 1)))

theorem integerSlicePoints_card_le_count
    (Y : Set (RatPoint n)) (B : ℝ)
    (a : IntPoint (n + 1)) (j : Fin (n + 1)) (hj : a j ≠ 0) (k : ℤ)
    (hmap : ∀ x ∈ integerSlicePoints X B a k,
      rationalPoint (deleteIntegerCoordinate j x) ∈ Y) :
    (integerSlicePoints X B a k).card ≤ count Y B := by
  apply Finset.card_le_card_of_injOn (deleteIntegerCoordinate j)
  · intro x hx
    exact mem_integralPoints.mpr
      ⟨fun i => (mem_integralPoints.mp (Finset.mem_filter.mp hx).1).1 (j.succAbove i),
        hmap x hx⟩
  · intro x hx y hy hxy
    exact deleteIntegerCoordinate_injective_on_level a j hj
      ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) hxy

