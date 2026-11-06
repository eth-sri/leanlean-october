/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Height.Box
public import CCDN.Hilbert.AffineCurveDegree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Ideal.Height
import CCDN.Algebra.PolynomialSection
import CCDN.Hilbert.PrimeComponentTranscendence

/-! The elementary linear box bound for prime curves in affine
three-space. A transcendental coordinate has fibers of size at most the
affine Hilbert degree, and the integer box has only 2 floor(B)+1 values
of that coordinate. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- CCDN's elementary degree-times-box-side bound, for rational
prime curves in affine three-space. -/
theorem curve_count_le_degree_mul_box_side
    (I : Ideal (CoordinatePolynomial 3)) [I.IsPrime]
    (hheight : I.height = 2) {d : ℕ} (hdegree : HasAffineCurveDegree I d)
    {B : ℝ} (hB : 0 ≤ B) :
    (count (idealZeroLocus I) B : ℝ) ≤ (d : ℝ) * (2 * B + 1) := by
  classical
  let S := integralPoints (idealZeroLocus I) B
  have hint : count (idealZeroLocus I) B ≤ d * (2 * ⌊B⌋ + 1).toNat := by
    by_cases hS : S.Nonempty
    · obtain ⟨x, hx⟩ := hS
      obtain ⟨j, hj⟩ := height_two_transcendental_coordinate_of_point I hheight
        (rationalPoint x) (mem_integralPoints.mp hx).2
      have hproper (t : ℚ) : X j - C t ∉ I := fun ht => hj <| by
        have hscalar : (Ideal.Quotient.mk I) (X j) =
            algebraMap ℚ (CoordinatePolynomial 3 ⧸ I) t := by
          simpa only [map_sub, Ideal.Quotient.algebraMap_eq] using
            sub_eq_zero.mp (Ideal.Quotient.eq_zero_iff_mem.mpr ht)
        rw [hscalar]; exact isAlgebraic_algebraMap t
      have hfiber (t : ℤ) : (S.filter (fun x => x j = t)).card ≤ d := by
        let T := S.filter (fun x => x j = t)
        have hh := polynomial_section_card_le_degree I d hdegree
          (X j - C (t : ℚ)) (hproper t) 1
          ((totalDegree_sub _ _).trans (max_le (by simp)
            (by change (C (t : ℚ) : CoordinatePolynomial 3).totalDegree ≤ 1; rw [totalDegree_C]; omega)))
          (fun x : T => rationalPoint x.val)
          (fun x y h => Subtype.ext (funext fun k => Int.cast_injective (congrFun h k)))
          (fun x => (mem_integralPoints.mp (Finset.mem_filter.mp x.property).1).2)
          fun x => by
            have ht := (Finset.mem_filter.mp x.property).2
            simp only [map_sub, eval_X, eval_C, rationalPoint, ht, sub_self]
        simpa only [Fintype.card_coe, Nat.mul_one] using hh
      have himage : (S.image (fun x => x j)).card ≤ (2 * ⌊B⌋ + 1).toNat := by
        have hh := Finset.card_le_card (show S.image (fun x => x j) ⊆ Finset.Icc (-⌊B⌋) ⌊B⌋ from
          fun t ht => by
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
            obtain ⟨hlo, hhi⟩ := abs_le.mp ((mem_integralPoints.mp hx).1 j)
            have hn : -(x j) ≤ ⌊B⌋ := Int.le_floor.mpr (by push_cast; linarith)
            exact Finset.mem_Icc.mpr ⟨by omega, Int.le_floor.mpr hhi⟩)
        rw [Int.card_Icc] at hh
        convert hh using 1; congr 1; omega
      exact (Finset.card_le_mul_card_image S d (fun t _ => hfiber t)).trans
        (Nat.mul_le_mul_left d himage)
    · change S.card ≤ _
      simp only [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty]
      exact Nat.zero_le _
  have hfloor : 0 ≤ ⌊B⌋ := Int.floor_nonneg.mpr hB
  have hside : ((2 * ⌊B⌋ + 1).toNat : ℝ) ≤ 2 * B + 1 := by
    rw [show (((2 * ⌊B⌋ + 1).toNat : ℕ) : ℝ) = 2 * (⌊B⌋ : ℝ) + 1 by
      exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ 2 * ⌊B⌋ + 1 by omega)]
    linarith [Int.floor_le B]
  exact (by exact_mod_cast hint : (count (idealZeroLocus I) B : ℝ) ≤
    (d : ℝ) * ((2 * ⌊B⌋ + 1).toNat : ℝ)).trans
    (mul_le_mul_of_nonneg_left hside (Nat.cast_nonneg _))

end
end CCDN
