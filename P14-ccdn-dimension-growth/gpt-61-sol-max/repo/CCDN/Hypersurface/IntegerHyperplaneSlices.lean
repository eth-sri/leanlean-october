/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Height.Box
import Mathlib.Algebra.BigOperators.Fin

/-! Counting bounded integral points by the integer values of a
linear form. Deleting a coordinate with nonzero coefficient is injective
on each level and preserves the box radius. -/

@[expose] public section
namespace CCDN

variable {n : ℕ}

/-- The value `∑ a i * x i` of the integer linear form with coefficients `a` at the point `x`. -/
noncomputable def integerLinearLevel  (a x : IntPoint n)  := ∑ i, a i * x i

/-- The projection of an integer point in `n + 1` coordinates to `n` coordinates by deleting
coordinate `j`. -/
noncomputable def deleteIntegerCoordinate  (j : Fin (n + 1))
    (x : IntPoint (n + 1)) : IntPoint n := fun i => x (j.succAbove i)

variable (X : Set (RatPoint n)) (B : ℝ) (a : IntPoint n)

/-- The integral points of `X` of height at most `B` on the level set `∑ a i * x i = k` of the
integer linear form with coefficients `a`. -/
noncomputable def integerSlicePoints   (k : ℤ) : Finset (IntPoint n) := by
  classical
  exact (integralPoints X B).filter fun x => integerLinearLevel a x = k

private noncomputable def integerSliceLevels   : Finset ℤ := by
  classical
  exact (integralPoints X B).image (integerLinearLevel a)

private theorem count_eq_sum_integerSlicePoints   :
    count X B = ∑ k ∈ integerSliceLevels X B a, (integerSlicePoints X B a k).card := by
  solve_by_elim [Finset.card_eq_sum_card_image]

private theorem integerLinearLevel_abs_le  (a x : IntPoint n) {H B : ℝ}
    (hH : 0 ≤ H) (ha : InBox a H)
    (hx : InBox x B) :
    |(integerLinearLevel a x : ℝ)| ≤ ↑n * H * B := by
  simp only [integerLinearLevel, Int.cast_sum, Int.cast_mul]
  calc
    |∑ i, (a i : ℝ) * (x i : ℝ)| ≤ ∑ i, |(a i : ℝ) * (x i : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, H * B := by
      grind [Finset.sum_le_sum, mul_le_mul]
    _ = _ := by simp [mul_assoc]


/-- Assembly over the levels of the integral point set. The sets
`Y k` can be the zero loci of the constructed hyperplane restrictions. -/
theorem count_le_of_integer_hyperplane_slices 
    (X : Set (RatPoint (n + 1))) (a : IntPoint (n + 1))
    (j : Fin (n + 1)) (hj : a j ≠ 0) (Y : ℤ → Set (RatPoint n))
    {H B K : ℝ} (hH : 0 ≤ H) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (ha : InBox a H)
    (hmap : ∀ k x, x ∈ integerSlicePoints X B a k →
      rationalPoint (deleteIntegerCoordinate j x) ∈ Y k)
    (hcount : ∀ k, (count (Y k) B : ℝ) ≤ K) :
    (count X B : ℝ) ≤ (2 * (n + 1 : ℕ) * H * B + 1) * K := by
  classical
  rw [count_eq_sum_integerSlicePoints X B a, Nat.cast_sum]
  calc
    _ ≤ ∑ _k ∈ integerSliceLevels X B a, K := by
      apply Finset.sum_le_sum
      intro k _
      exact ((Nat.cast_le (α := ℝ)).mpr
        ((by
           let inline_hmap := hmap k
           classical
           apply Finset.card_le_card_of_injOn (deleteIntegerCoordinate j)
           · intro x hx
             exact mem_integralPoints.mpr
               ⟨fun i => (mem_integralPoints.mp (Finset.mem_filter.mp hx).1).1 (j.succAbove i),
                 inline_hmap x hx⟩
           · intro x hx y hy hxy
             exact (by
                     let inline_hlevel := Eq.trans (Finset.mem_filter.mp hx).right (Eq.symm (Finset.mem_filter.mp hy).right)
                     have hrest : ∑ i : Fin n, a (j.succAbove i) * x (j.succAbove i) =
                         ∑ i : Fin n, a (j.succAbove i) * y (j.succAbove i) := by
                       apply Finset.sum_congr rfl
                       intro i _
                       rw [show x (j.succAbove i) = y (j.succAbove i) from congrFun hxy i]
                     have hpivot : x j = y j := by
                       unfold integerLinearLevel at inline_hlevel
                       rw [Fin.sum_univ_succAbove _ j, Fin.sum_univ_succAbove _ j] at inline_hlevel
                       exact mul_left_cancel₀ hj (by omega)
                     funext i
                     by_cases hi : i = j
                     · simpa only [hi] using hpivot
                     · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
                       exact congrFun hxy k)))).trans (hcount k)
    _ = ((integerSliceLevels X B a).card : ℝ) * K := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right ((by
                                           let inline_n := n + (1 : ℕ)
                                           classical
                                           let R : ℝ := ↑inline_n * H * B
                                           have hR : 0 ≤ R := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hH) hB
                                           have hsub : integerSliceLevels X B a ⊆ Finset.Icc (-⌊R⌋) ⌊R⌋ := by
                                             intro k hk
                                             obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
                                             have hb := integerLinearLevel_abs_le a x hH ha (mem_integralPoints.mp hx).1
                                             have hpos :=
                                               Int.le_floor.mpr (le_trans (le_abs_self _) hb)
                                             have hneg : -integerLinearLevel a x ≤ ⌊R⌋ :=
                                               Int.le_floor.mpr (by grind)
                                             exact Finset.mem_Icc.mpr ⟨by omega, hpos⟩
                                           have hcard := Finset.card_le_card hsub
                                           have hfloor := Int.floor_nonneg.mpr hR
                                           have hcast : (((⌊R⌋ + 1 - -⌊R⌋).toNat) : ℝ) =
                                               2 * (⌊R⌋ : ℝ) + 1 := by
                                             exact_mod_cast (show ((⌊R⌋ + 1 - -⌊R⌋).toNat : ℤ) = 2 * ⌊R⌋ + 1 by omega)
                                           rw [Int.card_Icc] at hcard
                                           have hr : ((integerSliceLevels X B a).card : ℝ) ≤
                                               (((⌊R⌋ + 1 - -⌊R⌋).toNat) : ℝ) := by exact_mod_cast hcard
                                           calc
                                             _ ≤ 2 * R + 1 := by linarith [Int.floor_le R]
                                             _ = _ := by dsimp [R]; ring)) hK

end CCDN
