/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Algebra.Equations
public import CCDN.ClassGroup.DescendedGeneratorCount
public import CCDN.AuxiliaryPolynomial.AffineScaledEstimate
public import CCDN.Plane.CurveCount
import CCDN.Algebra.FieldMapIrreducible
import CCDN.ClassGroup.OddDegreeNormCurveBaseChange
import CCDN.ClassGroup.SquareNormCurveIrreducibility
import CCDN.ClassGroup.OddDegreeNormCurveCount
import CCDN.ClassGroup.DiscriminantNumerics

@[expose] public section
namespace CCDN
noncomputable section
open NumberField Finset
open scoped nonZeroDivisors IntermediateField

lemma normCurveBoxHeight_root_le {n : ℕ} (hn : 2 ≤ n) {B : ℝ} (hB : 1 ≤ B) :
    (max (2 * B) (Real.sqrt (B ^ n))) ^ (1 / (n : ℝ)) ≤ 2 * Real.sqrt B := by
  have hs : 1 ≤ Real.sqrt B := by
    simpa using Real.sqrt_le_sqrt hB
  have hbase : 1 ≤ 2 * Real.sqrt B := by linarith
  have hsquare : (2 * Real.sqrt B) ^ 2 = 4 * B := by
    grind
  have hpower :=
    pow_le_pow_right₀ hbase hn
  have hH : max (2 * B) (Real.sqrt (B ^ n)) ≤ (2 * Real.sqrt B) ^ n := by
    apply max_le
    linarith
    · apply (Real.sqrt_le_left (pow_nonneg (by positivity) _)).mpr
      calc
        B ^ n ≤ ((2 * Real.sqrt B) ^ 2) ^ n :=
          pow_le_pow_left₀ (zero_le_one.trans hB) (by rw [hsquare]; linarith) n
        _ = ((2 * Real.sqrt B) ^ n) ^ 2 := by simp [← pow_mul, mul_comm n 2]
  have hh := Real.rpow_le_rpow (by positivity) hH (by positivity : 0 ≤ 1 / (n : ℝ))
  grind [one_div, Real.pow_rpow_inv_natCast]

private theorem boundedSquareNormTranslationClasses_uniform_count (K : Type*) [Field K] [NumberField K]
    {B : ℝ} (hB1 : 1 ≤ B)
    (hB : |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) ≤ B) :
    ((boundedSquareNormTranslationClasses K B).card : ℝ) * Real.sqrt |(discr K : ℝ)| ≤
      (numberFieldLatticeBoxConstant (Module.finrank ℚ K) ((Module.finrank ℚ K : ℝ) ^ 2) *
        (2 : ℝ) ^ Module.finrank ℚ K) * B ^ (Module.finrank ℚ K - 1) := by
  obtain ⟨b, hb, hnorm⟩ := exists_numberField_short_basis K
  apply boundedSquareNormTranslationClasses_count_of_relative_short_basis K b hb hB1
    (by positivity)
  exact fun i ↦ (hnorm i).trans (mul_le_mul_of_nonneg_left hB (by positivity))


def oddIndexNormCurveCountConstant : ℝ :=
  2 * affineHypersurfaceAuxiliaryConstant 0


/-- If `[K : ℚ(β)]` is odd, `n = [K : ℚ] ≥ 2` and `ε ≠ 0`, then the signed norm curve
`y ^ 2 = ε * N(x - β)` has at most `C * n ^ 3 * B ^ (1 / n) * (log B + n)` integral points of
height at most `B ≥ 1`. -/
theorem signed_norm_curve_count_of_odd_subfield_index
    (K : Type*) [Field K] [NumberField K]
    (β : 𝓞 K) {ε : ℤ} (hε : ε ≠ 0)
    (hn : 2 ≤ Module.finrank ℚ K)
    (hindex : Odd (Module.finrank ℚ⟮(β : K)⟯ K))
    {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus (rationalEquation
      (signedNormCurvePolynomial K β ε))) B : ℝ) ≤
      oddIndexNormCurveCountConstant * (Module.finrank ℚ K : ℝ) ^ 3 *
        B ^ (1 / (Module.finrank ℚ K : ℝ)) *
          (Real.log B + Module.finrank ℚ K) := by
  have hεQ : (ε : ℚ) ≠ 0 := by exact_mod_cast hε
  have hd := signedNormCurvePolynomial_map_totalDegree K ℚ β hεQ hn
  have hir : AbsolutelyIrreducibleRat
      (rationalEquation (signedNormCurvePolynomial K β ε)) :=
    (absolutelyIrreducibleRat_map_iff _).mpr
      (signedNormCurvePolynomial_absolute_irreducible_of_odd_subfield_index K β hε hindex)
  have h := plane_curve_count _ (mvPolynomial_irreducible_of_field_map _ _ hir) hB
  rw [hd] at h
  simpa only [curveBound, oddIndexNormCurveCountConstant, mul_assoc] using h


abbrev parityWeight (n : ℕ) (x : ℝ) := if Odd n then 1 else x
abbrev curveFiberCost (n : ℕ) := 16 * affineHypersurfaceAuxiliaryConstant 0 * (n:ℝ)^4
abbrev normBox (n : ℕ) (B : ℝ) := max (2*B) (Real.sqrt (B^n))

private lemma normCurveBoxHeight_log_le {n : ℕ} (hn : 2 ≤ n) {B : ℝ} (hB : 1 ≤ B) :
    Real.log (max (2 * B) (Real.sqrt (B ^ n))) + n ≤
      2 * (n : ℝ) * (Real.log B + 1) := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hbase : 1 ≤ 2 * B := by linarith
  have hpow : 1 ≤ B ^ n := one_le_pow₀ hB
  have hH : max (2 * B) (Real.sqrt (B ^ n)) ≤ (2 * B) ^ n := by
    apply max_le
    · simpa using pow_le_pow_right₀ hbase (by omega : 1 ≤ n)
    · have hs : Real.sqrt (B ^ n) ≤ B ^ n :=
        (Real.sqrt_le_left (by positivity)).mpr (by nlinarith)
      exact hs.trans (pow_le_pow_left₀ hB0.le (by linarith) n)
  have hlog := Real.log_le_log (show 0 < max (2 * B) (Real.sqrt (B ^ n)) from
    lt_of_lt_of_le (by positivity) (le_max_left _ _)) hH
  rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hB0.ne'] at hlog
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hlogB := Real.log_nonneg hB
  nlinarith

private lemma norm_curve_sign_bound (K : Type*) [Field K] [NumberField K] (hn : 2 ≤ fieldDegree K) {B : ℝ} (hB : 1 ≤ B)
    (z : 𝓞 K) (hgen : ℚ⟮(z : K)⟯ = ⊤) {ε : ℤ} (hε : IsUnit ε) :
    (count (signedNormCurveLocus K z ε) (normBox (fieldDegree K) B) : ℝ) ≤
      (8 * affineHypersurfaceAuxiliaryConstant 0 * (fieldDegree K:ℝ)^4) * Real.sqrt B * parityWeight (fieldDegree K) (Real.log B+1) := by
  let n := fieldDegree K
  let H := normBox n B
  have hH : 1 ≤ H := (show 1 ≤ 2*B by linarith).trans (le_max_left _ _)
  have hr := normCurveBoxHeight_root_le hn hB
  change H^(1/(n:ℝ)) ≤ 2*Real.sqrt B at hr
  have hc := (affineHypersurfaceAuxiliaryConstant_pos 0).le
  by_cases ho : Odd n
  · rw [parityWeight,ite_eq_left ho,mul_one]
    apply (signed_norm_curve_log_free_count K z hε hn ho hH).trans
    nlinarith only [mul_le_mul_of_nonneg_left hr (show 0 ≤ 3*affineHypersurfaceAuxiliaryConstant 0*(n:ℝ)^4 by positivity),
      show 0 ≤ affineHypersurfaceAuxiliaryConstant 0*(n:ℝ)^4*Real.sqrt B by positivity]
  · rw [parityWeight,ite_eq_right ho]
    have hi : Odd (Module.finrank ℚ⟮(z:K)⟯ K) := by rw [IntermediateField.finrank_eq_one_iff_eq_top.mpr hgen]; decide
    apply (signed_norm_curve_count_of_odd_subfield_index K z hε.ne_zero hn hi hH).trans
    have hl := normCurveBoxHeight_log_le hn hB
    have hh := mul_le_mul hr hl (by have := Real.log_nonneg hH; positivity) (by positivity)
    change 2 * affineHypersurfaceAuxiliaryConstant 0 * (n:ℝ)^3 * H^(1/(n:ℝ)) * (Real.log H+n) ≤ _
    linear_combination 2 * affineHypersurfaceAuxiliaryConstant 0 * (n:ℝ)^3 * hh

/-- Count the primitive generators fiberwise modulo integer translations. For one
translation class the two norm curves suffice; empty fibers incur no charge. -/
private theorem primitive_square_count (K : Type*) [Field K] [NumberField K] (hn : 2 ≤ fieldDegree K) {B : ℝ} (hB : 1 ≤ B)
    {ι : Type*} [Finite ι] (β : ι → 𝓞 K) (hi : Function.Injective β)
    (hz : ∀ i, β i ∈ boundedSquareNormIntegers K B) (hgen : ∀ i, ℚ⟮(-(β i : K))⟯ = ⊤) :
    (Nat.card ι : ℝ) ≤ (curveFiberCost (fieldDegree K)*Real.sqrt B * parityWeight (fieldDegree K) (Real.log B+1)) *
      (boundedSquareNormTranslationClasses K B).card := by
  let q (i) : boundedSquareNormTranslationClasses K B := ⟨β i,mem_image.mpr ⟨β i,(boundedSquareNormIntegers_finite K B).mem_toFinset.mpr (hz i),rfl⟩⟩
  have hc := (affineHypersurfaceAuxiliaryConstant_pos 0).le
  have hw : 0 ≤ parityWeight (fieldDegree K) (Real.log B+1) := by unfold parityWeight; split <;> linarith [Real.log_nonneg hB]
  apply (card_le_fiber_budget q (show 0 ≤ curveFiberCost (fieldDegree K)*Real.sqrt B * parityWeight (fieldDegree K) (Real.log B+1) by positivity) ?_).trans_eq (by simp)
  rintro Q ⟨j,hj⟩
  let z := -β j
  have hmem (i : {i // q i = Q}) : β i.val ∈ squareNormTranslateFiber K z B := by
    refine ⟨hz _,?_⟩
    have h : (β i.val : IntegerTranslationQuotient K) = β j := congrArg Subtype.val (i.property.trans hj.symm)
    obtain ⟨k,hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq_iff_sub_mem.mp h)
    exact ⟨k,by simpa [z,eq_sub_iff_add_eq,sub_eq_iff_eq_add] using hk.symm⟩
  let := (squareNormTranslateFiber_finite K z B).fintype
  have hl := Nat.card_le_card_of_injective (fun i : {i // q i = Q} => (⟨β i.val,hmem i⟩ : squareNormTranslateFiber K z B))
    (fun i j h => Subtype.ext (hi (congrArg Subtype.val h)))
  have hbound (w : InfinitePlace K) : w (z:K) ≤ B := by change w.val (-(β j : K)) ≤ B; rw [AbsoluteValue.map_neg]; exact (hz j).2.1 w
  have hpair := hl.trans (squareNormTranslateFiber_count_le K z hbound)
  have hp := norm_curve_sign_bound K hn hB z (hgen j) (ε := 1) isUnit_one
  have hm := norm_curve_sign_bound K hn hB z (hgen j) (ε := -1) (by simp)
  apply (Nat.cast_le (α := ℝ)).mpr hpair |>.trans
  rw [Nat.cast_add]; dsimp only [curveFiberCost]; linarith only [hp,hm]

abbrev primitiveClassCost (n : ℕ) := curveFiberCost n*(numberFieldLatticeBoxConstant n ((n:ℝ)^2)*2^n)*
    (3*(9:ℝ)^(n-1))*(Real.log 9+2)

private lemma balanced_log_weight {D : ℝ} (hD : 0 < D) (hl : 1 ≤ Real.log D) {n : ℕ} (hn : 0 < n) :
    parityWeight n (Real.log (9 * D^(1/(n:ℝ)))+1) ≤ (Real.log 9+2) * parityWeight n (Real.log D) := by
  have h9 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 9)
  unfold parityWeight; split
  · rw [mul_one]; linarith
  · rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hD _).ne',Real.log_rpow hD]
    have hh : 1/(n:ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hn)).mpr (by exact_mod_cast hn)
    nlinarith

theorem primitive_class_bound (K : Type*) [Field K] [NumberField K] (hn : 2 ≤ fieldDegree K)
    {ι : Type*} [Finite ι] (β : ι → 𝓞 K) (hi : Function.Injective β)
    (hz : ∀ i, β i ∈ boundedSquareNormIntegers K (balancedRadius K)) (hgen : ∀ i, ℚ⟮(-(β i : K))⟯ = ⊤) :
    (Nat.card ι : ℝ) ≤ primitiveClassCost (fieldDegree K) * absDiscriminant K ^ classExponent (fieldDegree K) * parityWeight (fieldDegree K) (Real.log (absDiscriminant K)) := by
  let n := fieldDegree K
  let B := balancedRadius K
  let D := absDiscriminant K
  let C := curveFiberCost n
  let A := numberFieldLatticeBoxConstant n ((n:ℝ)^2)*2^n
  have hD := one_le_abs_discr K
  have h0 : 0 < D := zero_lt_one.trans_le hD
  have hr : (1:ℝ) ≤ D^(1/(n:ℝ)) := Real.one_le_rpow hD (by positivity)
  have hR : D^(1/(n:ℝ)) ≤ B := by dsimp only [B,balancedRadius]; linarith
  have hB := hr.trans hR
  have hlog := one_le_log_abs_discr K hn
  have hW : 0 ≤ parityWeight n (Real.log B+1) := by unfold parityWeight; split <;> linarith [Real.log_nonneg hB]
  have hc := (affineHypersurfaceAuxiliaryConstant_pos 0).le
  have hC : 0 ≤ C := by dsimp [C,curveFiberCost]; positivity
  have hA : 0 ≤ A := mul_nonneg (numberFieldLatticeBoxConstant_nonneg _ (sq_nonneg _)) (by positivity)
  have ht := boundedSquareNormTranslationClasses_uniform_count K hB hR
  have hs := primitive_square_count K hn hB β hi hz hgen
  have hh := classGroup_discriminant_bound_of_balanced_radius (D := D) (n := n) h0 (by dsimp [n]; omega) (A := C*A*parityWeight n (Real.log B+1))
    (calc (Nat.card ι:ℝ)*Real.sqrt D ≤ _ := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg D)
          _ ≤ _ := by linear_combination C*Real.sqrt B*parityWeight n (Real.log B+1) * ht)
  have hw := balanced_log_weight h0 hlog (n := n) (by dsimp [n]; omega)
  apply hh.trans
  linear_combination (C*A*(3*(9:ℝ)^(n-1))*D^classExponent n) * hw

end
end CCDN
