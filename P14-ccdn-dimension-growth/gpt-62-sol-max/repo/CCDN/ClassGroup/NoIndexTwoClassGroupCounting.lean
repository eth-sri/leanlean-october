/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.SmallSubfieldIntegerCount
public import CCDN.Plane.CurveCount
import CCDN.ClassGroup.NormCurveReduction
import CCDN.ClassGroup.OddDegreeClassGroupCounting
import CCDN.ClassGroup.OddDegreeNormCurveBaseChange
import CCDN.ClassGroup.SquareNormCurveIrreducibility
import CCDN.Algebra.IntegerRationalIrreducibility

/-!
Counting the bounded square-norm integers in the absence of
an index-two subfield. Ordinary norm curves and small-subfield exceptions
are both counted by proved estimates.

Uniform counts for signed norm curves whose parameter generates a
subfield of odd index. The ambient field degree may be even.
-/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField IntermediateField

/-- The absolute constant in the count of integral points on signed norm curves whose parameter
generates a subfield of odd index. -/
def oddIndexNormCurveCountConstant : ℝ :=
  affinePlaneCountConstant

private lemma oddIndexNormCurveCountConstant_pos : 0 < oddIndexNormCurveCountConstant :=
  affinePlaneCountConstant_pos

/-- If `[K : ℚ(β)]` is odd, `n = [K : ℚ] ≥ 2` and `ε ≠ 0`, then the signed norm curve
`y ^ 2 = ε * N(x - β)` has at most `C * n ^ 3 * B ^ (1 / n) * (log B + n)` integral points of
height at most `B ≥ 1`. -/
theorem signed_norm_curve_count_of_odd_subfield_index
    (K : Type*) [Field K] [NumberField K]
    (β : 𝓞 K) {ε : ℤ} (hε : ε ≠ 0)
    (hn : 2 ≤ Module.finrank ℚ K)
    (hindex : Odd (Module.finrank ℚ⟮(β : K)⟯ K))
    {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ)
      (signedNormCurvePolynomial K β ε))) B : ℝ) ≤
      oddIndexNormCurveCountConstant * (Module.finrank ℚ K : ℝ) ^ 3 *
        B ^ (1 / (Module.finrank ℚ K : ℝ)) *
          (Real.log B + Module.finrank ℚ K) := by
  have hd := signedNormCurvePolynomial_map_totalDegree K ℚ β (by exact_mod_cast hε) hn
  have hir := rational_irreducible_of_charZero_map _
    (signedNormCurvePolynomial_absolute_irreducible_of_odd_subfield_index K β hε hindex)
  have h := affine_plane_equation_bound _ hir (by omega) hB
  rw [hd] at h
  simpa only [curveBound, oddIndexNormCurveCountConstant, mul_assoc] using h

end
end CCDN

namespace CCDN
noncomputable section
open NumberField NumberField.InfinitePlace
open scoped IntermediateField

variable (K : Type*) [Field K] [NumberField K]

private lemma even_index_translate_mem_smallSubfield
    (hnoTwo : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2)
    (β : 𝓞 K) (hindex : ¬ Odd (Module.finrank ℚ⟮(β : K)⟯ K))
    {B : ℝ} {α : 𝓞 K} (hα : α ∈ squareNormTranslateFiber K β B) :
    α ∈ boundedSmallSubfieldIntegers K B := by
  let L := ℚ⟮(β : K)⟯
  have he : Even (Module.finrank L K) := by
    aesop
  have hpos : 0 < Module.finrank L K := Module.finrank_pos
  have hne := hnoTwo L
  have hfour : 4 ≤ Module.finrank L K := by
    grind
  have hdim : 4 * Module.finrank ℚ L ≤ Module.finrank ℚ K := by
    have ht := Module.finrank_mul_finrank ℚ L K
    nlinarith
  refine ⟨hα.1.2.1, L, hdim, ?_⟩
  obtain ⟨x, hx⟩ := hα.2
  rw [hx]
  exact L.sub_mem (L.intCast_mem x) (IntermediateField.mem_adjoin_simple_self ℚ (β : K))

private lemma normCurveBoxHeight_log_le {n : ℕ} (hn : 2 ≤ n) {B : ℝ} (hB : 1 ≤ B) :
    Real.log (max (2 * B) (Real.sqrt (B ^ n))) + n ≤
      2 * (n : ℝ) * (Real.log B + 1) := by
  have hB0 := zero_lt_one.trans_le hB
  have hH := (show 0 < 2 * B by positivity).trans_le (le_max_left _ (Real.sqrt (B ^ n)))
  have hn0 : (0 : ℝ) < n := by positivity
  have h := Real.log_le_log (Real.rpow_pos_of_pos hH _) (normCurveBoxHeight_root_le hn hB)
  rw [Real.log_rpow hH, Real.log_mul (by norm_num) (Real.sqrt_ne_zero'.mpr hB0),
    Real.log_sqrt hB0.le, one_div, inv_mul_eq_div, div_le_iff₀ hn0] at h
  have htwo := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have hlog := Real.log_nonneg hB
  nlinarith [mul_nonneg hn0.le hlog, mul_nonneg hn0.le (show 0 ≤ 1 - Real.log 2 by linarith)]

/-- The degree-dependent constant bounding the contribution of one integer-translation class to the
bounded square-norm count for fields of degree `n` without an index-two subfield. -/
def noIndexTwoCurveContributionConstant (n : ℕ) : ℝ :=
  8 * oddIndexNormCurveCountConstant * (n : ℝ) ^ 4

/-- The constant `noIndexTwoCurveContributionConstant n` is nonnegative. -/
lemma noIndexTwoCurveContributionConstant_nonneg (n : ℕ) :
    0 ≤ noIndexTwoCurveContributionConstant n := by
  have := oddIndexNormCurveCountConstant_pos
  unfold noIndexTwoCurveContributionConstant
  positivity


/-- For a number field of degree `n ≥ 2` without an intermediate field of index two and `B ≥ 1`, the
number of bounded square-norm integers is at most the number of bounded integers in small
subfields plus `C(n)` times the number of translation classes times `√B * (log B + 1)`. -/
theorem boundedSquareNormIntegers_no_index_two_count
    (hnoTwo : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2)
    (hn : 2 ≤ Module.finrank ℚ K) {B : ℝ} (hB : 1 ≤ B) :
    ((boundedSquareNormIntegers K B).ncard : ℝ) ≤
      (boundedSmallSubfieldIntegers K B).ncard +
      noIndexTwoCurveContributionConstant (Module.finrank ℚ K) *
        (boundedSquareNormTranslationClasses K B).card *
          Real.sqrt B * (Real.log B + 1) := by
  let n := Module.finrank ℚ K
  let H := max (2 * B) (Real.sqrt (B ^ n))
  let A := oddIndexNormCurveCountConstant * (n : ℝ) ^ 3
  have hA : 0 ≤ A := by have := oddIndexNormCurveCountConstant_pos; positivity
  have hH : 1 ≤ H := (show 1 ≤ 2 * B by linarith).trans (le_max_left _ _)
  have hlog := Real.log_nonneg hB
  have hlogH := Real.log_nonneg hH
  have hh := squareNorm_count_le_of_curves K
    (C := A * ((2 * Real.sqrt B) * (2 * (n : ℝ) * (Real.log B + 1)))) (by positivity)
    _ (boundedSmallSubfieldIntegers_finite K B)
    (fun β => Odd (Module.finrank ℚ⟮(β : K)⟯ K))
    (fun β ho _ hx => even_index_translate_mem_smallSubfield K hnoTwo β ho hx)
    (fun β ε ho hε => by
      have hh := signed_norm_curve_count_of_odd_subfield_index K β hε.ne_zero hn ho hH
      rw [mul_assoc] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul (normCurveBoxHeight_root_le hn hB) (normCurveBoxHeight_log_le hn hB)
          (by positivity) (by positivity)) hA))
  convert hh using 1
  simp only [A, n, noIndexTwoCurveContributionConstant]
  ring

end
end CCDN
