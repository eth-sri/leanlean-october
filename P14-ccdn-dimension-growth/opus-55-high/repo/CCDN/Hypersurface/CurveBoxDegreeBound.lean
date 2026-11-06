/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.IdealZeroLocus
import CCDN.Height.Box
import CCDN.Hilbert.AffineCurveDegree
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Ideal.Height
import CCDN.Algebra.PolynomialSection
import CCDN.Hilbert.PrimeComponentTranscendence

/-! The elementary linear box bound for prime curves in affine
three-space. A transcendental coordinate has fibers of size at most the
affine Hilbert degree, and the integer box has only 2 floor(B)+1 values
of that coordinate. -/

namespace CCDN
section
open MvPolynomial

variable (I : Ideal (CoordinatePolynomial 3)) [I.IsPrime] (hheight : I.height = 2) {d : ℕ} (hdegree : HasAffineCurveDegree I d)
include hheight hdegree

theorem curve_count_le_degree_mul_integer_interval
    (B : ℝ) :
    count (idealZeroLocus I) B ≤ d * (2 * ⌊B⌋ + 1).toNat := by
  let S := integralPoints (idealZeroLocus I) B
  by_cases hS : S.Nonempty
  · obtain ⟨x, hx⟩ := hS
    obtain ⟨j, hj⟩ := height_two_transcendental_coordinate_of_point I hheight
      (rationalPoint x) (mem_integralPoints.mp hx).2
    have hproper (t : ℚ) : X j - C t ∉ I := by
      intro ht
      have he := Ideal.Quotient.eq_zero_iff_mem.mpr ht
      have hscalar : (Ideal.Quotient.mk I) (X j) =
          algebraMap ℚ (CoordinatePolynomial 3 ⧸ I) t := by
        simpa using sub_eq_zero.mp he
      apply hj
      rw [hscalar]
      exact isAlgebraic_algebraMap t
    have hfiber (t : ℤ) :
        (S.filter (fun x => x j = t)).card ≤ d := by
      let T := S.filter (fun x => x j = t)
      have hpoints : Function.Injective (fun x : T => rationalPoint x.val) := by
        intro x y h
        apply Subtype.ext
        funext k
        exact Int.cast_injective (congrFun h k)
      have hh := polynomial_section_card_le_degree I d hdegree
        (X j - C (t : ℚ)) (hproper t) 1
        (by
          apply (totalDegree_sub _ _).trans
          apply max_le
          · simp
          · change (C t : CoordinatePolynomial 3).totalDegree ≤ 1
            rw [totalDegree_C]
            omega)
        (fun x : T => rationalPoint x.val) hpoints
        (by
          intro x
          exact (mem_integralPoints.mp (Finset.mem_filter.mp x.property).1).2)
        (by
          intro x
          have ht := (Finset.mem_filter.mp x.property).2
          simp only [map_sub, eval_X, eval_C, rationalPoint, ht, sub_self])
      simpa using hh
    have himage : (S.image (fun x => x j)).card ≤ (2 * ⌊B⌋ + 1).toNat := by
      have hsub : S.image (fun x => x j) ⊆ Finset.Icc (-⌊B⌋) ⌊B⌋ := by
        intro t ht
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨hlo, hhi⟩ := abs_le.mp ((mem_integralPoints.mp hx).1 j)
        have hn : -(x j) ≤ ⌊B⌋ := Int.le_floor.mpr (by grind)
        exact Finset.mem_Icc.mpr ⟨by omega, Int.le_floor.mpr hhi⟩
      have hh := Finset.card_le_card hsub
      rw [Int.card_Icc] at hh
      grind
    exact (Finset.card_le_mul_card_image S d (fun t _ => hfiber t)).trans
      (Nat.mul_le_mul_left d himage)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hS
    change S.card ≤ _
    grind

/-- CCDN's elementary degree-times-box-side bound, for rational
prime curves in affine three-space. -/
theorem curve_count_le_degree_mul_box_side
    {B : ℝ} (hB : 0 ≤ B) :
    (count (idealZeroLocus I) B : ℝ) ≤ (d : ℝ) * (2 * B + 1) := by
  have hfloor := Int.floor_nonneg.mpr hB
  have hside : ((2 * ⌊B⌋ + 1).toNat : ℝ) ≤ 2 * B + 1 := by
    have he : (((2 * ⌊B⌋ + 1).toNat : ℕ) : ℝ) = 2 * (⌊B⌋ : ℝ) + 1 := by
      exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ 2 * ⌊B⌋ + 1 by omega))
    linarith [Int.floor_le B]
  calc
    _ ≤ d * ((2 * ⌊B⌋ + 1).toNat : ℝ) := by
      exact_mod_cast curve_count_le_degree_mul_integer_interval I hheight hdegree B
    _ ≤ _ := mul_le_mul_of_nonneg_left hside (Nat.cast_nonneg _)

