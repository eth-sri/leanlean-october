/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.Box
import Mathlib.Algebra.BigOperators.Fin

/-! Counting bounded integral points by the integer values of a
linear form. Deleting a coordinate with nonzero coefficient is injective
on each level and preserves the box radius. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The value `∑ a i * x i` of the integer linear form with coefficients `a` at the point `x`. -/
def integerLinearLevel {n : ℕ} (a x : IntPoint n) : ℤ := ∑ i, a i * x i

/-- The projection of an integer point in `n + 1` coordinates to `n` coordinates by deleting
coordinate `j`. -/
def deleteIntegerCoordinate {n : ℕ} (j : Fin (n + 1))
    (x : IntPoint (n + 1)) : IntPoint n := fun i => x (j.succAbove i)

/-- The integral points of `X` of height at most `B` on the level set `∑ a i * x i = k` of the
integer linear form with coefficients `a`. -/
noncomputable def integerSlicePoints {n : ℕ} (X : Set (RatPoint n))
    (B : ℝ) (a : IntPoint n) (k : ℤ) : Finset (IntPoint n) := by
  classical
  exact (integralPoints X B).filter fun x => integerLinearLevel a x = k

/-- Assembly over the levels of the integral point set. The sets
`Y k` can be the zero loci of the constructed hyperplane restrictions. -/
theorem count_le_of_integer_hyperplane_slices {n : ℕ}
    (X : Set (RatPoint (n + 1))) (a : IntPoint (n + 1))
    (j : Fin (n + 1)) (hj : a j ≠ 0) (Y : ℤ → Set (RatPoint n))
    {H B K : ℝ} (hH : 0 ≤ H) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (ha : InBox a H)
    (hmap : ∀ k x, x ∈ integerSlicePoints X B a k →
      rationalPoint (deleteIntegerCoordinate j x) ∈ Y k)
    (hcount : ∀ k, (count (Y k) B : ℝ) ≤ K) :
    (count X B : ℝ) ≤ (2 * (n + 1 : ℕ) * H * B + 1) * K := by
  classical
  let L := (integralPoints X B).image (integerLinearLevel a)
  let R : ℝ := (n + 1 : ℕ) * H * B
  have hR : 0 ≤ R := by positivity
  have hsub : L ⊆ Finset.Icc (-⌊R⌋) ⌊R⌋ := by
    rintro _ hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    have hb : |(integerLinearLevel a x : ℝ)| ≤ R := by
      simp only [integerLinearLevel, Int.cast_sum, Int.cast_mul, R]
      refine (Finset.abs_sum_le_sum_abs _ _).trans
        ((Finset.sum_le_sum fun i _ => (?_ : _ ≤ H * B)).trans_eq (by simp [mul_assoc]))
      rw [abs_mul]
      exact mul_le_mul (ha i) ((mem_integralPoints.mp hx).1 i) (abs_nonneg _) hH
    have hpos : integerLinearLevel a x ≤ ⌊R⌋ := Int.le_floor.mpr ((le_abs_self _).trans hb)
    have hneg : -integerLinearLevel a x ≤ ⌊R⌋ :=
      Int.le_floor.mpr (by simpa only [Int.cast_neg] using (neg_le_abs _).trans hb)
    exact Finset.mem_Icc.mpr ⟨by omega, hpos⟩
  have hfloor : 0 ≤ ⌊R⌋ := Int.floor_nonneg.mpr hR
  have hLcard : (L.card : ℝ) ≤ 2 * (n + 1 : ℕ) * H * B + 1 := by
    have hcard := Finset.card_le_card hsub
    rw [Int.card_Icc] at hcard
    have hr : (L.card : ℝ) ≤ (((⌊R⌋ + 1 - -⌊R⌋).toNat : ℕ) : ℝ) := mod_cast hcard
    rw [show (((⌊R⌋ + 1 - -⌊R⌋).toNat : ℕ) : ℝ) = 2 * (⌊R⌋ : ℝ) + 1 from
      mod_cast (show ((⌊R⌋ + 1 - -⌊R⌋).toNat : ℤ) = 2 * ⌊R⌋ + 1 by omega)] at hr
    exact (hr.trans (by linarith [Int.floor_le R] : 2 * (⌊R⌋ : ℝ) + 1 ≤ 2 * R + 1)).trans_eq
      (by dsimp [R]; ring)
  have hslice (k : ℤ) : ((integerSlicePoints X B a k).card : ℝ) ≤ K := by
    refine (show ((integerSlicePoints X B a k).card : ℝ) ≤ count (Y k) B from mod_cast ?_).trans
      (hcount k)
    refine Finset.card_le_card_of_injOn (deleteIntegerCoordinate j)
      (fun x hx => mem_integralPoints.mpr
        ⟨fun i => (mem_integralPoints.mp (Finset.mem_filter.mp hx).1).1 (j.succAbove i),
          hmap k x hx⟩)
      fun x hx y hy hxy => ?_
    have hlevel := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    have hrest : ∑ i : Fin n, a (j.succAbove i) * x (j.succAbove i) =
        ∑ i : Fin n, a (j.succAbove i) * y (j.succAbove i) :=
      Finset.sum_congr rfl fun i _ => by
        rw [show x (j.succAbove i) = y (j.succAbove i) from congrFun hxy i]
    have hpivot : x j = y j := by
      unfold integerLinearLevel at hlevel
      rw [Fin.sum_univ_succAbove _ j, Fin.sum_univ_succAbove _ j] at hlevel
      exact mul_left_cancel₀ hj (by omega)
    funext i
    by_cases hi : i = j
    · simpa only [hi] using hpivot
    · obtain ⟨m, rfl⟩ := Fin.exists_succAbove_eq hi
      exact congrFun hxy m
  rw [show count X B = ∑ k ∈ L, (integerSlicePoints X B a k).card from
    Finset.card_eq_sum_card_image (integerLinearLevel a) (integralPoints X B), Nat.cast_sum]
  exact ((Finset.sum_le_sum fun k _ => hslice k).trans_eq (by simp)).trans
    (mul_le_mul_of_nonneg_right hLcard hK)

end
end CCDN
