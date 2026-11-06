/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.SmallSubfieldIntegerCount
public import CCDN.Plane.AffineNonzeroConstant
import CCDN.ClassGroup.NormCurveExceptionalReduction
import CCDN.ClassGroup.OddDegreeClassGroupCounting
import CCDN.ClassGroup.OddDegreeNormCurveBaseChange
import CCDN.ClassGroup.SquareNormCurveIrreducibility
import CCDN.Plane.CurveCount

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
open NumberField NumberField.InfinitePlace
open scoped NumberField IntermediateField

/-- The absolute constant in the count of integral points on signed norm curves whose parameter
generates a subfield of odd index. -/
def oddIndexNormCurveCountConstant : ℝ :=
  2 * Real.exp 1 * affineNonzeroConstantBound planeResidueConstant

/-- The degree-dependent constant bounding the contribution of one integer-translation class to the
bounded square-norm count for fields of degree `n` without an index-two subfield. -/
def noIndexTwoCurveContributionConstant (n : ℕ) : ℝ :=
  8 * oddIndexNormCurveCountConstant * (n : ℝ) ^ 4

/-- The constant `noIndexTwoCurveContributionConstant n` is nonnegative. -/
lemma noIndexTwoCurveContributionConstant_nonneg (n : ℕ) :
    0 ≤ noIndexTwoCurveContributionConstant n := by
  have := affineNonzeroConstantBound_pos planeResidueConstant
  unfold noIndexTwoCurveContributionConstant oddIndexNormCurveCountConstant; positivity

variable (K : Type*) [Field K] [NumberField K]

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
  /- If `[K : ℚ(β)]` is odd, `n = [K : ℚ] ≥ 2` and `ε ≠ 0`, then the signed norm curve
  `y ^ 2 = ε * N(x - β)` has at most `C * n ^ 3 * B ^ (1 / n) * (log B + n)` integral points of
  height at most `B ≥ 1`. -/
  obtain ⟨β, _, _, hcover⟩ := exists_norm_curve_exception_split K hnoTwo B
  let n := Module.finrank ℚ K
  let H := max (2 * B) (Real.sqrt (B ^ n))
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hH : 1 ≤ H := le_trans (by linarith) (le_max_left _ _)
  have hsc (b : 𝓞 K) {ε : ℤ} (hε : ε ≠ 0) (hindex : Odd (Module.finrank ℚ⟮(b : K)⟯ K)) :
      (count (signedNormCurveLocus K b ε) H : ℝ) ≤
        oddIndexNormCurveCountConstant * (n : ℝ) ^ 3 * H ^ (1 / (n : ℝ)) * (Real.log H + n) := by
    have hd := signedNormCurvePolynomial_map_totalDegree K ℚ b (mod_cast hε) hn
    have h := count_rational_plane_of_residue_bound _
      ((absolutelyIrreducibleRat_map_iff _).mpr
        (signedNormCurvePolynomial_absolute_irreducible_of_odd_subfield_index K b hε hindex))
      (by omega) hH planeResidueConstant_pos.le planeResidueBound
    rw [hd] at h
    simpa only [signedNormCurveLocus, n, curveBound, oddIndexNormCurveCountConstant, mul_assoc]
      using h
  have hroot := normCurveBoxHeight_root_le hn hB
  have hlog : Real.log H + n ≤ 2 * (n : ℝ) * (Real.log B + 1) := by
    have hpow : 1 ≤ B ^ n := one_le_pow₀ hB
    have hH_le : H ≤ (2 * B) ^ n := max_le
      (by simpa using pow_le_pow_right₀ (by linarith : 1 ≤ 2 * B) (by omega : 1 ≤ n))
      (((Real.sqrt_le_left (by positivity)).mpr (by nlinarith)).trans
        (pow_le_pow_left₀ hB0.le (by linarith) n))
    have hlogH := Real.log_le_log (by linarith) hH_le
    rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hB0.ne'] at hlogH
    have htwo : Real.log (2 : ℝ) ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n, Real.log_nonneg hB]
  have hC : 0 ≤ oddIndexNormCurveCountConstant * (n : ℝ) ^ 3 := by
    have := affineNonzeroConstantBound_pos planeResidueConstant
    unfold oddIndexNormCurveCountConstant; positivity
  have hmain : 0 ≤ noIndexTwoCurveContributionConstant n * Real.sqrt B * (Real.log B + 1) :=
    mul_nonneg (mul_nonneg (noIndexTwoCurveContributionConstant_nonneg n)
      (Real.sqrt_nonneg B)) (by linarith [Real.log_nonneg hB])
  have hpair (q : boundedSquareNormTranslationClasses K B) :
      ((if Odd (Module.finrank ℚ⟮(β q : K)⟯ K) then
        count (signedNormCurveLocus K (β q) 1) H +
          count (signedNormCurveLocus K (β q) (-1)) H else 0 : ℕ) : ℝ) ≤
      noIndexTwoCurveContributionConstant n * Real.sqrt B * (Real.log B + 1) := by
    by_cases ho : Odd (Module.finrank ℚ⟮(β q : K)⟯ K)
    · simp only [ite_eq_left ho, Nat.cast_add]
      have hp := hsc (β q) (ε := 1) (by norm_num) ho
      have hm := hsc (β q) (ε := -1) (by norm_num) ho
      have hprod := mul_le_mul hroot hlog (by linarith [Real.log_nonneg hH, Nat.cast_nonneg (α := ℝ) n])
        (by positivity)
      exact (by linarith : _ ≤ 2 * (oddIndexNormCurveCountConstant * (n : ℝ) ^ 3) *
        (H ^ (1 / (n : ℝ)) * (Real.log H + n))).trans
        ((mul_le_mul_of_nonneg_left hprod (by positivity)).trans_eq
          (by unfold noIndexTwoCurveContributionConstant; ring))
    · simpa only [ite_eq_right ho, Nat.cast_zero] using hmain
  have hcoverR : ((boundedSquareNormIntegers K B).ncard : ℝ) ≤
      (boundedSmallSubfieldIntegers K B).ncard +
        ∑ q : boundedSquareNormTranslationClasses K B,
          ((if Odd (Module.finrank ℚ⟮(β q : K)⟯ K) then
            count (signedNormCurveLocus K (β q) 1) H +
              count (signedNormCurveLocus K (β q) (-1)) H else 0 : ℕ) : ℝ) := mod_cast hcover
  exact (hcoverR.trans (add_le_add le_rfl (Finset.sum_le_sum fun q _ => hpair q))).trans_eq
    (by simp; ring)

end
end CCDN
