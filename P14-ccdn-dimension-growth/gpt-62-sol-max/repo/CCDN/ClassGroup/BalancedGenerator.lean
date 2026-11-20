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

section Discriminant

variable (K : Type*) [Field K] [NumberField K]

/-- The absolute discriminant, as the absolute value of an integer cast to `ℕ` and to `ℝ`. -/
lemma numberField_discriminant_natAbs_cast :
    ((discr K).natAbs : ℝ) = |(discr K : ℝ)| := by
  simp

/-- The absolute discriminant `(discr K).natAbs` of a number field is positive. -/
lemma numberField_discriminant_natAbs_pos : 0 < (discr K).natAbs :=
  Int.natAbs_pos.mpr (discr_ne_zero K)

/-- The absolute discriminant of a number field is at least `1`. -/
lemma one_le_abs_discr : 1 ≤ |(discr K : ℝ)| := by
  exact_mod_cast Int.one_le_abs (discr_ne_zero K)

/-- A number field of degree at least `2` over `ℚ` has absolute discriminant at least `3`. -/
lemma three_le_abs_discr (hn : 2 ≤ Module.finrank ℚ K) : 3 ≤ |(discr K : ℝ)| := by
  have hh : (3 : ℤ) ≤ |discr K| := by
    have := abs_discr_gt_two (K := K) (by omega : 1 < Module.finrank ℚ K)
    omega
  exact_mod_cast hh

/-- A number field of degree at least `2` over `ℚ` has logarithmic absolute discriminant
`log |discr K| ≥ 1`. -/
lemma one_le_log_abs_discr (hn : 2 ≤ Module.finrank ℚ K) :
    1 ≤ Real.log |(discr K : ℝ)| := by
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
    (Real.exp_one_lt_three.le.trans (three_le_abs_discr K hn))

end Discriminant

private lemma prod_weighted_sqrt_radii {ι : Type*} [Fintype ι]
    (u : ι → ℝ≥0) (m : ι → ℕ) (T : ℝ≥0) :
    (∏ i, (T / NNReal.sqrt (u i)) ^ m i) =
      T ^ (∑ i, m i) / NNReal.sqrt (∏ i, u i ^ m i) := by
  classical
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  congr 1
  change (∏ i, (NNReal.sqrtHom (u i)) ^ m i) = NNReal.sqrtHom (∏ i, u i ^ m i)
  simp only [map_prod, map_pow]

variable (K : Type*) [Field K] [NumberField K]

private lemma principal_square_infinite_product (I : Ideal (𝓞 K)) {α : 𝓞 K}
    (hIα : I ^ 2 = Ideal.span {α}) :
    (∏ w : InfinitePlace K, w (α : K) ^ mult w) = (Ideal.absNorm I : ℝ) ^ 2 := by
  rw [prod_eq_abs_norm, ← Algebra.coe_norm_int]
  norm_cast
  rw [← Int.natCast_natAbs, generator_absolute_norm_of_ideal_square K I hIα,
    Nat.cast_pow]

private lemma inverse_ideal_minkowskiBound_toReal (I : (Ideal (𝓞 K))⁰) :
    (mixedEmbedding.minkowskiBound K (FractionalIdeal.mk0 K I)⁻¹).toReal =
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)⁻¹ *
        (2⁻¹ : ℝ) ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| *
          2 ^ Module.finrank ℚ K := by
  classical
  simp only [mixedEmbedding.minkowskiBound,
    mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis,
    mixedEmbedding.volume_fundamentalDomain_latticeBasis,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.coe_toReal, ENNReal.toReal_ofNat, mixedEmbedding.finrank]
  rw [ENNReal.toReal_ofReal
    (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _))]
  simp only [Units.val_inv_eq_inv_val, map_inv₀, FractionalIdeal.coe_mk0,
    FractionalIdeal.coeIdeal_absNorm, Rat.cast_inv, Rat.cast_natCast,
    Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  ring

private lemma square_generator_radius_product (I : Ideal (𝓞 K)) {α : 𝓞 K}
    (hIα : I ^ 2 = Ideal.span {α}) (T : ℝ≥0) :
    (∏ w : InfinitePlace K,
      (T / NNReal.sqrt (Real.toNNReal (w (α : K)))) ^ mult w) =
      T ^ Module.finrank ℚ K / (Ideal.absNorm I : ℝ≥0) := by
  rw [prod_weighted_sqrt_radii
    (fun w : InfinitePlace K ↦ Real.toNNReal (w (α : K))) mult T,
    sum_mult_eq]
  have hp : (∏ w : InfinitePlace K,
      Real.toNNReal (w (α : K)) ^ mult w) =
      (Ideal.absNorm I : ℝ≥0) ^ 2 := by
    apply NNReal.coe_injective
    simpa only [NNReal.coe_prod, NNReal.coe_pow,
      Real.coe_toNNReal _ (apply_nonneg _ _), NNReal.coe_natCast]
      using principal_square_infinite_product K I hIα
  simp_all

/-- Every two-torsion class admits an integral square generator bounded
at every infinite place by nine times the discriminant root. -/
private theorem exists_balanced_two_torsion_square_generator
    (c : classGroupTwoTorsion K) :
    ∃ J : (Ideal (𝓞 K))⁰, ∃ β : 𝓞 K,
      ClassGroup.mk0 J = c ∧ β ≠ 0 ∧
      (J : Ideal (𝓞 K)) ^ 2 = Ideal.span {β} ∧
      (Algebra.norm ℤ β).natAbs = Ideal.absNorm (J : Ideal (𝓞 K)) ^ 2 ∧
      ∀ w : InfinitePlace K,
        w (β : K) < 9 * |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  classical
  obtain ⟨I, hIc⟩ := ClassGroup.mk0_surjective (c : ClassGroup (𝓞 K))
  obtain ⟨α, hα, hIα⟩ := exists_generator_of_class_square_eq_one I (by aesop)
  let n := Module.finrank ℚ K
  let D := |(discr K : ℝ)|
  let T : ℝ≥0 := ⟨3 * Real.sqrt (D ^ (1 / (n : ℝ))), by positivity⟩
  have hn : 0 < n := Module.finrank_pos
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hD : 0 < D := zero_lt_one.trans_le (one_le_abs_discr K)
  have hT : (2 : ℝ) ^ n * Real.sqrt D < (T : ℝ) ^ n := by
    change _ < (3 * Real.sqrt (D ^ (1 / (n : ℝ)))) ^ n
    rw [mul_pow, Real.sqrt_eq_rpow (D ^ (1 / (n : ℝ))),
      ← Real.rpow_mul_natCast (by positivity : 0 ≤ D ^ (1 / (n : ℝ))),
      ← Real.rpow_mul hD.le, show (1 / (n : ℝ)) * (1 / 2 * n) = 1 / 2 by field_simp,
      ← Real.sqrt_eq_rpow]
    gcongr
    norm_num
  have hT2 : (T : ℝ) ^ 2 = 9 * D ^ (1 / (n : ℝ)) := by
    change (3 * Real.sqrt (D ^ (1 / (n : ℝ)))) ^ 2 = _
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    norm_num
  let f : InfinitePlace K → ℝ≥0 :=
    fun w ↦ T / NNReal.sqrt (Real.toNNReal (w (α : K)))
  have hN : 0 < (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I
  have hprod : (∏ w : InfinitePlace K, f w ^ mult w) =
      T ^ Module.finrank ℚ K / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ≥0) :=
    square_generator_radius_product K _ hIα T
  have hm : mixedEmbedding.minkowskiBound K (FractionalIdeal.mk0 K I)⁻¹ <
      volume (mixedEmbedding.convexBodyLT K f) := by
    rw [mixedEmbedding.convexBodyLT_volume, ← ENNReal.coe_mul, hprod]
    apply (ENNReal.toReal_lt_toReal
      (mixedEmbedding.minkowskiBound_lt_top K _).ne ENNReal.coe_ne_top).mp
    rw [inverse_ideal_minkowskiBound_toReal, ENNReal.coe_toReal]
    push_cast
    have hc : (2⁻¹ : ℝ) ^ nrComplexPlaces K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hf : (1 : ℝ) ≤ mixedEmbedding.convexBodyLTFactor K := by
      exact_mod_cast mixedEmbedding.one_le_convexBodyLTFactor K
    calc
      _ ≤ (2 : ℝ) ^ n * Real.sqrt D / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) := by
        linear_combination ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)⁻¹ * Real.sqrt D * 2 ^ n) * hc
      _ < (T : ℝ) ^ n / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) := div_lt_div_of_pos_right hT hN
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hf
  obtain ⟨κ, hκI, hκ, hκw⟩ :=
    mixedEmbedding.exists_ne_zero_mem_ideal_lt K (FractionalIdeal.mk0 K I)⁻¹ hm
  obtain ⟨J, β, hJ, hβ, heq, hsq⟩ :=
    rescale_integral_ideal_square (K := K) I hα hIα hκ hκI
  refine ⟨J, β, hJ.trans hIc, hβ, hsq, generator_absolute_norm_of_ideal_square K J hsq, fun w ↦ ?_⟩
  have hw : 0 < w (α : K) := InfinitePlace.pos_iff.mpr (by simpa using hα)
  have hk : w κ < (T : ℝ) / Real.sqrt (w (α : K)) := by
    simpa [f, apply_nonneg] using hκw w
  change (β : K) = (α : K) * κ ^ 2 at heq
  rw [heq, map_mul, map_pow, ← hT2]
  have h := pow_lt_pow_left₀ ((lt_div_iff₀ (Real.sqrt_pos.mpr hw)).mp hk)
    (by positivity) (by decide : (2 : ℕ) ≠ 0)
  rwa [mul_pow, Real.sq_sqrt hw.le, mul_comm (w κ ^ 2)] at h

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
  choose J β hc hβ hsq hnorm hbound using
    exists_balanced_two_torsion_square_generator K
  refine ⟨β, ?_, fun c ↦ ⟨hβ c, hbound c, J c, hc c, hsq c, hnorm c⟩⟩
  intro c e hce
  apply Subtype.ext
  rw [← hc c, ← hc e]
  exact ideal_class_eq_of_square_generators_eq (J c) (J e) (hsq c) (hsq e) hce

end
end CCDN
