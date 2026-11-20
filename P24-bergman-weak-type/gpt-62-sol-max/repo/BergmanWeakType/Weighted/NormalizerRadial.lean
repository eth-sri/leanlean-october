/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.Normalizer
public import BergmanWeakType.Weighted.PolarPotential
public import BergmanWeakType.Weighted.AngleMeasure
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # The circular normalizer as a polar kernel potential -/

@[expose] public section

noncomputable section

open MeasureTheory Real Set

namespace BergmanWeakType.Weighted

abbrev boundaryMeasure : Measure ℂ := angleMeasure.map (circleMap 0 1)

theorem ae_norm_boundaryMeasure : ∀ᵐ w ∂boundaryMeasure, ‖w‖ = 1 :=
  (ae_map_iff (continuous_circleMap 0 1).measurable.aemeasurable (measurableSet_eq_fun measurable_norm measurable_const)).mpr
    (.of_forall fun _ ↦ by simp)

def boundarySource : PolarSource :=
  ⟨boundaryMeasure, ae_norm_boundaryMeasure.mono (fun _ hw ↦ by simp [hw]),
    inferInstance⟩

private theorem boundaryIntegral_eq_normalizer (α r θ : ℝ) :
    boundarySource.integral (polarKernel (-(α + 2) / 2)) r θ = normalizer α r := by
  have hc := circleAverage_weightedKernel_norm α (circleMap 0 r θ) 1
  simp only [one_mul, norm_circleMap_zero] at hc
  have habs : normalizer α |r| = normalizer α r := by
    simp [normalizer]
  rw [habs, circleAverage_eq_integral_angleMeasure] at hc
  change (∫ w, polarKernel (-(α + 2) / 2) w r θ ∂boundaryMeasure) = _
  unfold boundaryMeasure
  rw [integral_map (continuous_circleMap 0 1).measurable.aemeasurable
    (show Measurable (fun w : ℂ ↦ polarKernel (-(α + 2) / 2) w r θ) by
      unfold polarKernel polarDenominator radialComponent
      fun_prop).aestronglyMeasurable]
  simpa only [Function.comp_apply, polarKernel_eq_norm_weightedKernel] using hc

def normalizerFirst (α r : ℝ) : ℝ :=
  boundarySource.integral (polarKernelD .radial (-(α + 2) / 2)) r 0

def normalizerSecond (α r : ℝ) : ℝ :=
  boundarySource.integral (polarKernelDD .radial (-(α + 2) / 2)) r 0

theorem normalizer_hasDerivAt (α : ℝ) {r : ℝ} (hr : r ^ 2 < 1) :
    HasDerivAt (normalizer α) (normalizerFirst α r) r := by
  simpa only [Axis.HasDeriv, Axis.slice, Axis.coord, boundaryIntegral_eq_normalizer, normalizerFirst] using
    boundarySource.integral_kernel_hasDerivAt .radial (-(α + 2) / 2) hr 0

theorem normalizerFirst_hasDerivAt (α : ℝ) {r : ℝ} (hr : r ^ 2 < 1) :
    HasDerivAt (normalizerFirst α) (normalizerSecond α r) r :=
  boundarySource.integral_kernelD_hasDerivAt .radial (-(α + 2) / 2) hr 0

theorem continuousOn_normalizer (α : ℝ) : ContinuousOn (normalizer α) (radii) :=
  fun _ hr ↦ (normalizer_hasDerivAt α (sq_lt_one_of_mem_Ico hr)).continuousAt.continuousWithinAt

theorem continuousOn_normalizerFirst (α : ℝ) : ContinuousOn (normalizerFirst α) (radii) :=
  fun _ hr ↦ (normalizerFirst_hasDerivAt α (sq_lt_one_of_mem_Ico hr)).continuousAt.continuousWithinAt

theorem continuousOn_normalizerSecond (α : ℝ) : ContinuousOn (normalizerSecond α) (radii) :=
  (boundarySource.cont_integral (A := univ) (PolarSource.cont_kernelDD .radial _)).uncurry_right 0 (mem_univ _)

/-- The exact radial differential equation for the normalizing circular average. -/
theorem normalizer_ode (α : ℝ) {r : ℝ} (hr : r ^ 2 < 1) (hr0 : r ≠ 0) :
    polarOperator (α + 2) r (normalizer α r) (normalizerFirst α r) (normalizerSecond α r) 0 = 0 := by
  let q := -(α + 2) / 2
  have h0 : boundarySource.integral (polarKernel q) r = fun _ ↦ normalizer α r :=
    funext (boundaryIntegral_eq_normalizer α r)
  have ht (θ : ℝ) := (boundarySource.integral_kernel_hasDerivAt .angular q hr θ).deriv
  simp only [Axis.slice, Axis.coord, h0, deriv_const] at ht
  have htt := (boundarySource.integral_kernelD_hasDerivAt .angular q hr 0).deriv
  simp only [Axis.slice, Axis.coord, funext fun θ ↦ (ht θ).symm, deriv_const] at htt
  dsimp only [q] at htt
  have he := boundarySource.operator_eq (α + 2) hr hr0 0
  rw [integral_eq_zero_of_ae (μ := boundarySource.μ) (ae_norm_boundaryMeasure.mono fun _ hw ↦ by simp [hw]), mul_zero] at he
  simpa only [PolarSource.potentialOperator, boundaryIntegral_eq_normalizer,
    normalizerFirst, normalizerSecond, ← htt] using he

theorem normalizer_pos (α : ℝ) {r : ℝ} (hr : r ∈ radii) : 0 < normalizer α r := by
  rw [← boundaryIntegral_eq_normalizer α r 0]
  have hp := ae_norm_boundaryMeasure.mono fun w hw ↦
    rpow_pos_of_pos (polarDenominator_pos (sq_lt_one_of_mem_Ico hr) hw.le 0) (-(α + 2) / 2)
  apply integral_pos_iff_support_of_nonneg_ae (hp.mono fun _ h ↦ h.le)
    (boundarySource.integrable_kernel (PolarSource.cont_kernel _) (sq_lt_one_of_mem_Ico hr) 0) |>.mpr
  rw [Function.support, measure_congr (ae_eq_univ.mpr (hp.mono fun _ h ↦ h.ne')), measure_univ]
  exact zero_lt_one

private theorem eq_at_zero_of_hasDerivAt_zero {f : ℝ → ℝ}
    (hc : ContinuousOn f (radii)) (hd : ∀ x ∈ openRadii, HasDerivAt f 0 x)
    {x : ℝ} (hx : x ∈ radii) : f x = f 0 := by
  apply sub_eq_zero.mp
  symm
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
    (hc.mono (fun y hy ↦ ⟨hy.1, hy.2.trans_lt hx.2⟩))
    (fun y hy ↦ hd y ⟨hy.1, hy.2.trans hx.2⟩) intervalIntegrable_const


/-- The radial equations with parameters `α` and `-(α+2)` are conjugated by
multiplication by `(1 - r²)^(α+1)`. The conjugated Wronskian vanishes at zero. -/
theorem radialMass_mul_normalizer (α : ℝ) {r : ℝ} (hr : r ∈ radii) :
    (1 - r ^ 2) ^ (α + 1) * normalizer α r =
      normalizer (-(α + 2)) r := by
  let β := -(α + 2)
  let W := fun x : ℝ ↦ x * (1 - x ^ 2) *
    (normalizerFirst β x * normalizer α x - normalizer β x * normalizerFirst α x) +
    2 * (α + 1) * (x ^ 2 * (normalizer β x * normalizer α x))
  have hA := continuousOn_normalizer α
  have hB := continuousOn_normalizer β
  have hA' := continuousOn_normalizerFirst α
  have hB' := continuousOn_normalizerFirst β
  have hW : ∀ x ∈ radii, W x = 0 := by
    intro x hx
    rw [eq_at_zero_of_hasDerivAt_zero (f := W) (by fun_prop) _ hx]
    · simp [W]
    intro x hx
    have hx' := sq_lt_one_of_mem_Ico (Ioo_subset_Ico_self hx)
    have d := hasDerivAt_id x
    have dA := normalizer_hasDerivAt α hx'
    have dB := normalizer_hasDerivAt β hx'
    have dA' := normalizerFirst_hasDerivAt α hx'
    have dB' := normalizerFirst_hasDerivAt β hx'
    have h := ((d.mul ((d.pow 2).const_sub 1)).mul ((dB'.mul dA).sub (dB.mul dA'))).add
      (((d.pow 2).mul (dB.mul dA)).const_mul (2 * (α + 1)))
    have h1 := normalizer_ode α hx' hx.1.ne'
    have h2 := normalizer_ode β hx' hx.1.ne'
    convert h using 1
    · rfl
    simp only [polarOperator, radialCoeff, mul_zero, add_zero, β] at h1 h2
    dsimp [β]
    linear_combination normalizer (-(α + 2)) x * h1 - normalizer α x * h2
  let T := fun x : ℝ ↦ (1 - x ^ 2) ^ (α + 1)
  have ht {x : ℝ} (hx : x ∈ radii) := radial_defect_pos hx
  have hd (x : ℝ) (hx : x ∈ radii) :=
    mul_ne_zero (rpow_pos_of_pos (ht hx) (α + 1)).ne' (normalizer_pos α hx).ne'
  have hR : normalizer β r / (T r * normalizer α r) = 1 := by
    rw [eq_at_zero_of_hasDerivAt_zero (f := fun x ↦ normalizer β x / (T x * normalizer α x)) (hB.div ((continuousOn_radialRpow (α + 1)).mul hA) hd) _ hr]
    · simp [T]
    intro x hx
    have hx' := Ioo_subset_Ico_self hx
    have hs := sq_lt_one_of_mem_Ico hx'
    have dT := (((hasDerivAt_id x).pow 2).const_sub 1).rpow_const (p := α + 1)
      (Or.inl (ht hx').ne')
    convert (normalizer_hasDerivAt β hs).div (dT.mul (normalizer_hasDerivAt α hs)) (hd x hx') using 1
    · rfl
    dsimp only [Pi.pow_apply, Pi.sub_apply, Pi.mul_apply, id_eq]
    rw [rpow_sub_one (ht hx').ne']
    symm
    apply div_eq_zero_iff.mpr
    left
    field_simp [(ht hx').ne']
    grind
  grind

end BergmanWeakType.Weighted
