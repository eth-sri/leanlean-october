/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.PositiveRoot
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! # Reverse Jensen for negative powers and bounded-cutoff inverse moments

For a finite nonzero measure `ν` and `q > 0`, Hölder's inequality with the two factors `f ^ a`
and `f ^ (-a)` for `a = q / (q + 1)` bounds the `(-q)`-th power of `∫ f dν` by
`ν univ ^ (-q - 1) * ∫ f ^ (-q) dν`. Applied pointwise in the sample to the Wick density of the
regularized GMC, and combined with the exact Gaussian moments of the Wick density, this bounds
every inverse moment of the cutoff mass of a set of positive finite reference mass.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- Hölder step of reverse Jensen: if `f` is almost everywhere finite and nonzero, then
`ν univ ≤ (∫ f)^(q/(q+1)) * (∫ f^(-q))^(1/(q+1))`. -/
theorem reverseJensen_measure_univ_le_holder
    {S : Type*} [MeasurableSpace S] (ν : Measure S)
    (f : S → ℝ≥0∞) (hf : AEMeasurable f ν) (q : ℝ) (hq : 0 < q)
    (h0 : ∀ᵐ x ∂ν, f x ≠ 0) (htop : ∀ᵐ x ∂ν, f x ≠ ⊤) :
    ν Set.univ ≤
      (∫⁻ x, f x ∂ν) ^ (q / (q + 1)) * (∫⁻ x, (f x) ^ (-q) ∂ν) ^ (1 / (q + 1)) := by
  have hq1 : 0 < q + 1 := by linarith
  have hab : q / (q + 1) + 1 / (q + 1) = 1 := by
    field_simp
  have hH := ENNReal.lintegral_mul_norm_pow_le hf (hf.pow_const (-q)) (div_nonneg hq.le hq1.le) (div_nonneg zero_le_one hq1.le) hab
  have hone : ∀ᵐ x ∂ν, f x ^ (q / (q + 1)) * (f x ^ (-q)) ^ (1 / (q + 1)) = 1 := by
    filter_upwards [h0, htop] with x hx0 hxt
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ hx0 hxt]
    have h : q / (q + 1) + -q * (1 / (q + 1)) = 0 := by
      field_simp
      ring
    simp_all
  calc ν Set.univ = ∫⁻ _, 1 ∂ν := lintegral_one.symm
    _ = ∫⁻ x, f x ^ (q / (q + 1)) * (f x ^ (-q)) ^ (1 / (q + 1)) ∂ν :=
        lintegral_congr_ae (hone.mono fun _ hx => hx.symm)
    _ ≤ _ := hH

/-- Algebraic rearrangement of the Hölder bound into the reverse Jensen inequality. -/
theorem reverseJensen_rearrange (N J I : ℝ≥0∞) (q : ℝ) (hq : 0 < q)
    (hN0 : N ≠ 0) (hNt : N ≠ ⊤) (hJt : J ≠ ⊤)
    (h : N ≤ J ^ (q / (q + 1)) * I ^ (1 / (q + 1))) :
    J ^ (-q) ≤ N ^ (-q - 1) * I := by
  have hq1 : 0 < q + 1 := by linarith
  have h1 : N ^ (q + 1) ≤ J ^ q * I := by
    have h2 := ENNReal.rpow_le_rpow h hq1.le
    rwa [ENNReal.mul_rpow_of_nonneg _ _ hq1.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      div_mul_cancel₀ _ hq1.ne', one_div_mul_cancel hq1.ne', ENNReal.rpow_one] at h2
  have hJ0 : J ≠ 0 := by
    aesop
  have hNq : N ^ (q + 1) ≠ 0 := by positivity
  have hNqt : N ^ (q + 1) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hq1.le hNt
  have hJq : J ^ q ≠ 0 := by positivity
  rw [show -q - 1 = -(q + 1) by ring, ENNReal.rpow_neg, ENNReal.rpow_neg]
  calc (J ^ q)⁻¹ = (N ^ (q + 1))⁻¹ * N ^ (q + 1) * (J ^ q)⁻¹ := by
        rw [ENNReal.inv_mul_cancel hNq hNqt, one_mul]
    _ ≤ (N ^ (q + 1))⁻¹ * (J ^ q * I) * (J ^ q)⁻¹ := by gcongr
    _ = (N ^ (q + 1))⁻¹ * I * (J ^ q * (J ^ q)⁻¹) := by ring
    _ = (N ^ (q + 1))⁻¹ * I := by rw [ENNReal.mul_inv_cancel hJq (ENNReal.rpow_ne_top_of_nonneg hq.le hJt), mul_one]

/-- Reverse Jensen for negative powers: for a finite nonzero measure, the `(-q)`-th power of the
integral is at most `ν univ ^ (-q-1)` times the integral of the `(-q)`-th power. -/
theorem ennreal_lintegral_rpow_neg_le
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (f : S → ℝ≥0∞) (hf : AEMeasurable f ν) (q : ℝ) (hq : 0 < q) :
    (∫⁻ x, f x ∂ν) ^ (-q) ≤ (ν Set.univ) ^ (-q - 1) * ∫⁻ x, (f x) ^ (-q) ∂ν := by
  have hN0 : ν Set.univ ≠ 0 := by simp_all
  have hNt : ν Set.univ ≠ ⊤ := measure_ne_top ν _
  have hc : (ν Set.univ) ^ (-q - 1) ≠ 0 := by
    positivity
  by_cases hI : ∫⁻ x, (f x) ^ (-q) ∂ν = ⊤
  · simp_all
  by_cases hJ : ∫⁻ x, f x ∂ν = ⊤
  · simp_all
  have hf0 : ∀ᵐ x ∂ν, f x ≠ 0 := by
    filter_upwards [ae_lt_top' (hf.pow_const (-q)) hI] with x hx hx0
    simp_all
  have hft : ∀ᵐ x ∂ν, f x ≠ ⊤ := by
    filter_upwards [ae_lt_top' hf hJ] with x hx using hx.ne
  exact reverseJensen_rearrange _ _ _ q hq hN0 hNt hJ
    (reverseJensen_measure_univ_le_holder ν f hf q hq hf0 hft)
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- The `(-q)`-th power of the cutoff mass of `A` is bounded, pointwise in the sample, by the
reference mass of `A` to the power `-q - 1` times the reference integral of the `(-q)`-th power
of the Wick density. -/
theorem reverseJensen_mass_rpow_neg_le
    [SFinite P] (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r q : ℝ) (hq : 0 < q)
    (A : Set ℂ) (hA : MeasurableSet A) (hA0 : gmcReferenceMeasure A ≠ 0)
    (hAtop : gmcReferenceMeasure A ≠ ⊤) (ω : Ω) :
    (regularizedGMC P Xc γ r ω A) ^ (-q) ≤
      (gmcReferenceMeasure A) ^ (-q - 1) *
        ∫⁻ x in A, (gmcCircleWickDensity P Xc γ r ω x) ^ (-q) ∂gmcReferenceMeasure := by
  have hfin : IsFiniteMeasure (gmcReferenceMeasure.restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hAtop.lt_top⟩
  have hν0 : gmcReferenceMeasure.restrict A ≠ 0 := by
    simp_all
  have hW : AEMeasurable (gmcCircleWickDensity P Xc γ r ω)
      (gmcReferenceMeasure.restrict A) :=
    ((measurable_gmcCircleWickDensity P X Xc hXc γ r).comp
      (measurable_const.prodMk measurable_id)).aemeasurable
  rw [regularizedGMC_mass_eq_wick_lintegral P X Xc hXc γ r A hA ω]
  have h := ennreal_lintegral_rpow_neg_le (gmcReferenceMeasure.restrict A) hν0 _ hW q hq
  simp_all
section
variable (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r q V : ℝ) (hq : 0 < q) (A : Set ℂ) (hA : MeasurableSet A)
include hX hXc hq hA

/-- Integrating the Wick density moments over a set on which the circle variance is bounded by
`V` bounds the double integral of the `(-q)`-th power of the Wick density. -/
theorem reverseJensen_double_lintegral_le
    (hAtop : gmcReferenceMeasure A ≠ ⊤)
    (hV : ∀ x ∈ A, gaussianVariance P (fun ω => Xc ω x r) ≤ V) :
    ∫⁻ ω, ∫⁻ x in A, (gmcCircleWickDensity P Xc γ r ω x) ^ (-q) ∂gmcReferenceMeasure ∂P ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * (q ^ 2 + q) / 2 * V)) * gmcReferenceMeasure A := by
  have hP : IsProbabilityMeasure P := hX.1
  have hfin : IsFiniteMeasure (gmcReferenceMeasure.restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hAtop.lt_top⟩
  have hmeas : Measurable (Function.uncurry fun (ω : Ω) (x : ℂ) =>
      (gmcCircleWickDensity P Xc γ r ω x) ^ (-q)) :=
    ENNReal.continuous_rpow_const.measurable.comp
      (measurable_gmcCircleWickDensity P X Xc hXc γ r)
  have hc : 0 ≤ γ ^ 2 * (q ^ 2 + q) / 2 :=
    by positivity
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  calc _ ≤ ∫⁻ _ in A, ENNReal.ofReal _
        ∂gmcReferenceMeasure := by
        apply setLIntegral_mono' hA
        intro x hx
        rw [gmcCircleWickDensity_moment P X hX Xc hXc γ r (-q) x]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
        rw [show γ ^ 2 * ((-q) ^ 2 - -q) / 2 = γ ^ 2 * (q ^ 2 + q) / 2 by ring]
        bound
    _ = _ := setLIntegral_const ..

/-- At a fixed cutoff, every inverse moment of the cutoff mass of a set of positive finite
reference mass is bounded by the reference mass and the largest circle variance on the set. -/
theorem regularizedGMC_inverse_moment_le_variance
    (hA0 : gmcReferenceMeasure A ≠ 0)
    (hAtop : gmcReferenceMeasure A ≠ ⊤)
    (hV : ∀ x ∈ A, gaussianVariance P (fun ω => Xc ω x r) ≤ V) :
    ∫⁻ ω, (regularizedGMC P Xc γ r ω A) ^ (-q) ∂P ≤
      (gmcReferenceMeasure A) ^ (-q) * ENNReal.ofReal (Real.exp (γ ^ 2 * (q ^ 2 + q) / 2 * V)) := by
  have hP : IsProbabilityMeasure P := hX.1
  have hcoef : (gmcReferenceMeasure A) ^ (-q - 1) ≠ ⊤ :=
    by simp_all
  have hpow : (gmcReferenceMeasure A) ^ (-q) =
      (gmcReferenceMeasure A) ^ (-q - 1) * gmcReferenceMeasure A := by
    calc (gmcReferenceMeasure A) ^ (-q) = (gmcReferenceMeasure A) ^ ((-q - 1) + 1) := by
          simp
      _ = (gmcReferenceMeasure A) ^ (-q - 1) * (gmcReferenceMeasure A) ^ 1 :=
          ENNReal.rpow_add _ _ hA0 hAtop
      _ = _ := by simp
  calc ∫⁻ ω, (regularizedGMC P Xc γ r ω A) ^ (-q) ∂P
      ≤ ∫⁻ ω, (gmcReferenceMeasure A) ^ (-q - 1) *
          ∫⁻ x in A, (gmcCircleWickDensity P Xc γ r ω x) ^ (-q) ∂gmcReferenceMeasure ∂P :=
        lintegral_mono (reverseJensen_mass_rpow_neg_le P X Xc hXc γ r q hq A hA hA0 hAtop)
    _ = (gmcReferenceMeasure A) ^ (-q - 1) *
          ∫⁻ ω, ∫⁻ x in A, (gmcCircleWickDensity P Xc γ r ω x) ^ (-q)
            ∂gmcReferenceMeasure ∂P := lintegral_const_mul' _ _ hcoef
    _ ≤ (gmcReferenceMeasure A) ^ (-q - 1) *
          (ENNReal.ofReal _ * gmcReferenceMeasure A) := by
        gcongr
        exact reverseJensen_double_lintegral_le P X hX Xc hXc γ r q V hq A hA hAtop hV
    _ = (gmcReferenceMeasure A) ^ (-q) *
          ENNReal.ofReal _ := by
        rw [hpow]
        ring

end

end

end DOZZ.Proofs
