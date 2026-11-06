/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.TwoTorsion
import CCDN.ClassGroup.IdealRescaling
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Balanced square generators for two-torsion ideal classes.
The anisotropic Minkowski argument is applied to the inverse ideal; the
rescaling retains the exact generator needed for bounds at every place. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField nonZeroDivisors Real
open NumberField NumberField.InfinitePlace
open MeasureTheory MeasureTheory.Measure
open NNReal

variable (K : Type*) [Field K] [NumberField K]

/-- The absolute discriminant, as the absolute value of an integer cast to `ℕ` and to `ℝ`. -/
lemma numberField_discriminant_natAbs_cast :
    ((discr K).natAbs : ℝ) = |(discr K : ℝ)| := by
  simpa only [Int.cast_natCast, Int.cast_abs] using
    congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (discr K))

/-- The absolute discriminant `(discr K).natAbs` of a number field is positive. -/
lemma numberField_discriminant_natAbs_pos : 0 < (discr K).natAbs :=
  Int.natAbs_pos.mpr (discr_ne_zero K)

/-- The absolute discriminant of a number field is at least `1`. -/
lemma one_le_abs_discr : 1 ≤ |(discr K : ℝ)| :=
  mod_cast Int.one_le_abs (discr_ne_zero K)

/-- A number field of degree at least `2` over `ℚ` has absolute discriminant at least `3`. -/
lemma three_le_abs_discr (hn : 2 ≤ Module.finrank ℚ K) : 3 ≤ |(discr K : ℝ)| := by
  have := abs_discr_gt_two (K := K) (by omega : 1 < Module.finrank ℚ K)
  exact_mod_cast (by omega : (3 : ℤ) ≤ |discr K|)

/-- A number field of degree at least `2` over `ℚ` has logarithmic absolute discriminant
`log |discr K| ≥ 1`. -/
lemma one_le_log_abs_discr (hn : 2 ≤ Module.finrank ℚ K) :
    1 ≤ Real.log |(discr K : ℝ)| := by
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
    (Real.exp_one_lt_three.le.trans (three_le_abs_discr K hn))

/-- The bounded generators can be chosen injectively; equality of generators
forces equality of the corresponding ideals and hence of their ideal classes. -/
theorem exists_injective_balanced_two_torsion_generators :
    ∃ β : classGroupTwoTorsion K → 𝓞 K, Function.Injective β ∧
      ∀ c, β c ≠ 0 ∧
        (∀ w : InfinitePlace K, w (β c : K) <
          9 * |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ))) ∧
        ∃ J : (Ideal (𝓞 K))⁰, ClassGroup.mk0 J = c ∧
          (J : Ideal (𝓞 K)) ^ 2 = Ideal.span {β c} ∧
          (Algebra.norm ℤ (β c)).natAbs = Ideal.absNorm (J : Ideal (𝓞 K)) ^ 2 := by
  classical
  have hex (c : classGroupTwoTorsion K) :
      ∃ J : (Ideal (𝓞 K))⁰, ∃ β : 𝓞 K,
        ClassGroup.mk0 J = c ∧ β ≠ 0 ∧
        (J : Ideal (𝓞 K)) ^ 2 = Ideal.span {β} ∧
        (Algebra.norm ℤ β).natAbs = Ideal.absNorm (J : Ideal (𝓞 K)) ^ 2 ∧
        ∀ w : InfinitePlace K,
          w (β : K) < 9 * |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) := by
    obtain ⟨I, α, hIc, hα, hIα, _, _⟩ :=
      exists_two_torsion_integral_square_representative K c
    have hD : 0 < |(discr K : ℝ)| := zero_lt_one.trans_le (one_le_abs_discr K)
    have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
    have hn0 : (Module.finrank ℚ K : ℝ) ≠ 0 := mod_cast hn.ne'
    let T : ℝ≥0 := ⟨3 * |(discr K : ℝ)| ^ (1 / (2 * (Module.finrank ℚ K : ℝ))), by positivity⟩
    have hTn : (T : ℝ) ^ Module.finrank ℚ K = 3 ^ Module.finrank ℚ K * Real.sqrt |(discr K : ℝ)| := by
      change (3 * |(discr K : ℝ)| ^ (1 / (2 * (Module.finrank ℚ K : ℝ)))) ^ Module.finrank ℚ K = _
      rw [mul_pow, ← Real.rpow_natCast (|(discr K : ℝ)| ^ (1 / (2 * (Module.finrank ℚ K : ℝ)))) _,
        ← Real.rpow_mul hD.le,
        show 1 / (2 * (Module.finrank ℚ K : ℝ)) * (Module.finrank ℚ K : ℝ) = 1 / 2 by field_simp,
        ← Real.sqrt_eq_rpow]
    have hT2 : (T : ℝ) ^ 2 = 9 * |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) := by
      change (3 * |(discr K : ℝ)| ^ (1 / (2 * (Module.finrank ℚ K : ℝ)))) ^ 2 = _
      rw [mul_pow, ← Real.rpow_natCast (|(discr K : ℝ)| ^ (1 / (2 * (Module.finrank ℚ K : ℝ)))) 2,
        ← Real.rpow_mul hD.le]
      norm_num only [Nat.cast_ofNat]
      rw [show 1 / (2 * (Module.finrank ℚ K : ℝ)) * (2 : ℝ) = 1 / (Module.finrank ℚ K : ℝ) by ring]
    have hT : (2 : ℝ) ^ Module.finrank ℚ K * Real.sqrt |(discr K : ℝ)| <
        (T : ℝ) ^ Module.finrank ℚ K := by
      rw [hTn]
      exact mul_lt_mul_of_pos_right
        (pow_lt_pow_left₀ (by norm_num : (2 : ℝ) < 3) (by norm_num) hn.ne') (Real.sqrt_pos.mpr hD)
    let f : InfinitePlace K → ℝ≥0 := fun w ↦ T / NNReal.sqrt (Real.toNNReal (w (α : K)))
    have hN : 0 < (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) :=
      mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I
    have hprod : (∏ w : InfinitePlace K, f w ^ mult w) =
        T ^ Module.finrank ℚ K / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ≥0) := by
      have hrad : (∏ w : InfinitePlace K, f w ^ mult w) =
          T ^ (∑ w : InfinitePlace K, mult w) /
            NNReal.sqrt (∏ w : InfinitePlace K, Real.toNNReal (w (α : K)) ^ mult w) := by
        simp_rw [f, div_pow]
        rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
        congr 1
        change (∏ w, (NNReal.sqrtHom (Real.toNNReal (w (α : K)))) ^ mult w) =
          NNReal.sqrtHom (∏ w, Real.toNNReal (w (α : K)) ^ mult w)
        simp only [map_prod, map_pow]
      have hp : (∏ w : InfinitePlace K, Real.toNNReal (w (α : K)) ^ mult w) =
          (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ≥0) ^ 2 := by
        apply NNReal.coe_injective
        simpa only [NNReal.coe_prod, NNReal.coe_pow, Real.coe_toNNReal _ (apply_nonneg _ _),
          NNReal.coe_natCast] using (by
            rw [prod_eq_abs_norm, ← Algebra.coe_norm_int]
            norm_cast
            rw [← Int.natCast_natAbs, generator_absolute_norm_of_ideal_square K _ hIα, Nat.cast_pow] :
            (∏ w : InfinitePlace K, w (α : K) ^ mult w) = (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ 2)
      rw [hrad, sum_mult_eq, hp, NNReal.sqrt_sq]
    have hvol : volume (mixedEmbedding.convexBodyLT K f) =
        ((mixedEmbedding.convexBodyLTFactor K *
          (T ^ Module.finrank ℚ K / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ≥0)) : ℝ≥0) : ENNReal) := by
      rw [mixedEmbedding.convexBodyLT_volume, ← ENNReal.coe_mul, hprod]
    have hmink : (mixedEmbedding.minkowskiBound K (FractionalIdeal.mk0 K I)⁻¹).toReal =
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)⁻¹ *
          (2⁻¹ : ℝ) ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| *
            2 ^ Module.finrank ℚ K := by
      simp only [mixedEmbedding.minkowskiBound,
        mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis,
        mixedEmbedding.volume_fundamentalDomain_latticeBasis,
        ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
        ENNReal.coe_toReal, ENNReal.toReal_ofNat, mixedEmbedding.finrank]
      rw [ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _))]
      simp only [Units.val_inv_eq_inv_val, map_inv₀, FractionalIdeal.coe_mk0,
        FractionalIdeal.coeIdeal_absNorm, Rat.cast_inv, Rat.cast_natCast,
        Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
      ring
    have hm : mixedEmbedding.minkowskiBound K (FractionalIdeal.mk0 K I)⁻¹ <
        volume (mixedEmbedding.convexBodyLT K f) := by
      apply (ENNReal.toReal_lt_toReal
        (ne_of_lt (mixedEmbedding.minkowskiBound_lt_top K _)) (by rw [hvol]; finiteness)).mp
      rw [hmink, hvol, ENNReal.coe_toReal,
        NNReal.coe_mul, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast]
      have hc : (2⁻¹ : ℝ) ^ nrComplexPlaces K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      calc
        _ ≤ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)⁻¹ *
            Real.sqrt |(discr K : ℝ)| * 2 ^ Module.finrank ℚ K := by
          gcongr
          simpa using mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hN.le)
        _ = ((2 : ℝ) ^ Module.finrank ℚ K * Real.sqrt |(discr K : ℝ)|) /
            (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) := by ring
        _ < (T : ℝ) ^ Module.finrank ℚ K /
            (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) := div_lt_div_of_pos_right hT hN
        _ ≤ _ := le_mul_of_one_le_left (by positivity)
          (NNReal.coe_le_coe.mpr (mixedEmbedding.one_le_convexBodyLTFactor K))
    obtain ⟨κ, hκI, hκ, hκw⟩ :=
      mixedEmbedding.exists_ne_zero_mem_ideal_lt K (FractionalIdeal.mk0 K I)⁻¹ hm
    obtain ⟨J, β, hJ, hβ, heq, hsq, _⟩ :=
      rescale_integral_ideal_square (K := K) I hα hIα hκ hκI
    refine ⟨J, β, hJ.trans hIc, hβ, hsq,
      generator_absolute_norm_of_ideal_square K _ hsq, fun w ↦ ?_⟩
    have hαw : 0 < w (α : K) :=
      InfinitePlace.pos_iff.mpr (by simpa only [ne_eq, RingOfIntegers.coe_eq_zero_iff] using hα)
    have hk : w κ < (T : ℝ) / Real.sqrt (w (α : K)) := by
      simpa only [f, NNReal.coe_div, Real.coe_sqrt, Real.coe_toNNReal _ (apply_nonneg _ _)] using hκw w
    change (β : K) = (α : K) * κ ^ 2 at heq
    rw [heq, map_mul, map_pow, ← hT2]
    exact (mul_lt_mul_of_pos_left
      (pow_lt_pow_left₀ hk (apply_nonneg _ _) (by decide : (2 : ℕ) ≠ 0)) hαw).trans_eq
      (by rw [div_pow, Real.sq_sqrt hαw.le]; field_simp)
  choose J β hc hβ hsq hnorm hbound using hex
  refine ⟨β, fun c e hce => Subtype.ext ?_, fun c ↦ ⟨hβ c, hbound c, J c, hc c, hsq c, hnorm c⟩⟩
  rw [← hc c, ← hc e]
  exact ideal_class_eq_of_square_generators_eq (J c) (J e) (hsq c) (hsq e) hce

end
end CCDN
