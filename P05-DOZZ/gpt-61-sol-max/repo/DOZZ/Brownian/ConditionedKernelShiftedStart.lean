/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelShiftedRatio
public import DOZZ.Brownian.ConditionedKernelProbability
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Integral

/-!
# Shifted stochastic order for conditioned transition kernels

The positive-drift start comparison for conditioned Brownian kernels shifts the larger-start
endpoint left by the difference in starting states. The shifted likelihood ratio is antitone, and
the shifted law's mass below zero supplies the other half of the single-crossing argument.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory Set Topology
open scoped ENNReal

namespace DOZZ.Proofs

/-- State likelihood ratio after shifting the endpoint of the larger-start kernel. -/
noncomputable def conditionedKernelShiftedStartDensityRatio
    (ν c c' t d y : ℝ) : ℝ :=
  Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
    (Real.sinh (ν * (y + d)) / Real.sinh (ν * y)) *
      (Real.sinh (c * (y + d)) / Real.sinh (c' * y))

private theorem conditionedKernelShiftedStartDensityRatio_hasDerivAt
    {ν c c' t d y : ℝ} (hν : 0 < ν) (hc' : 0 < c') (hc : 0 < c)
    (hy : 0 < y) (hd : 0 ≤ d) :
    HasDerivAt (conditionedKernelShiftedStartDensityRatio ν c c' t d)
      (conditionedKernelShiftedStartDensityRatio ν c c' t d y *
        (-(d / t) +
          (conditionedKernelScore ν (y + d) - conditionedKernelScore ν y) +
          (conditionedKernelScore c (y + d) - conditionedKernelScore c' y))) y := by
  have hlinear : HasDerivAt (fun z : ℝ => -(d / t) * z - d ^ 2 / (2 * t))
      (-(d / t)) y := by
    convert ((hasDerivAt_id y).const_mul (-(d / t))).sub_const (d ^ 2 / (2 * t)) using 1 <;> simp
  have hexp := (Real.hasDerivAt_exp _).comp y hlinear
  have hνratio := hasDerivAt_sinhShift_ratio hν hν hy hd
  have hstateRatio := hasDerivAt_sinhShift_ratio hc' hc hy hd
  have hprod := (hexp.mul hνratio).mul hstateRatio
  convert hprod using 1
  · ext z
    simp [conditionedKernelShiftedStartDensityRatio]
  · dsimp [conditionedKernelShiftedStartDensityRatio]
    ring_nf

/-- The shifted start likelihood ratio is antitone when `d = x - x'`. Its derivative is bounded
by `-d/t + (x-x')/t = 0`, using the score's state monotonicity and parameter Lipschitz bound. -/
theorem conditionedKernelShiftedStartDensityRatio_antitoneOn
    {ν c c' t d : ℝ} (hν : 0 < ν) (hc' : 0 < c') (hcc' : c' ≤ c)
    (_ht : 0 < t) (hd : 0 ≤ d) (hshift : d / t = c - c') :
    AntitoneOn (conditionedKernelShiftedStartDensityRatio ν c c' t d) (Set.Ioi 0) := by
  have hc  := lt_of_lt_of_le hc' hcc'
  have hcont : ContinuousOn (conditionedKernelShiftedStartDensityRatio ν c c' t d)
      (Set.Ioi 0) := by
    change ContinuousOn (fun y : ℝ =>
      Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
        (Real.sinh (ν * (y + d)) / Real.sinh (ν * y)) *
          (Real.sinh (c * (y + d)) / Real.sinh (c' * y))) (Set.Ioi 0)
    have hExp : Continuous (fun y : ℝ =>
        Real.exp (-(d / t) * y - d ^ 2 / (2 * t))) := by fun_prop
    have hnum1 : Continuous (fun y : ℝ => Real.sinh (ν * (y + d))) := by fun_prop
    have hden1 : Continuous (fun y : ℝ => Real.sinh (ν * y)) := by fun_prop
    have hratio1 : ContinuousOn (fun y : ℝ =>
        Real.sinh (ν * (y + d)) / Real.sinh (ν * y)) (Set.Ioi 0) := by
      apply hnum1.continuousOn.div hden1.continuousOn
      intro y hy
      exact (Real.sinh_pos_iff.mpr (mul_pos hν (by simpa using hy))).ne'
    have hnum2 : Continuous (fun y : ℝ => Real.sinh (c * (y + d))) := by fun_prop
    have hden2 : Continuous (fun y : ℝ => Real.sinh (c' * y)) := by fun_prop
    have hratio2 : ContinuousOn (fun y : ℝ =>
        Real.sinh (c * (y + d)) / Real.sinh (c' * y)) (Set.Ioi 0) := by
      apply hnum2.continuousOn.div hden2.continuousOn
      intro y hy
      exact (Real.sinh_pos_iff.mpr (mul_pos hc' (by simpa using hy))).ne'
    exact (hExp.continuousOn.mul hratio1).mul hratio2
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0) hcont
  · intro y hy
    exact (conditionedKernelShiftedStartDensityRatio_hasDerivAt hν hc' hc
      (by simpa using hy) hd).differentiableAt.differentiableWithinAt
  · intro y hy
    have hypos : 0 < y := by simpa using hy
    rw [(conditionedKernelShiftedStartDensityRatio_hasDerivAt hν hc' hc hypos hd).deriv]
    have hνstate : conditionedKernelScore ν (y + d) - conditionedKernelScore ν y ≤ 0 := by
      have hanti := (conditionedKernelScore_strictAntiOn_state hν).antitoneOn
      exact sub_nonpos.mpr (hanti (Set.mem_Ioi.mpr hypos)
        (Set.mem_Ioi.mpr (by linarith [hd])) (by linarith))
    have hmixed := conditionedKernelScore_mixed_increment_upper hc' hypos
      (z := y + d) (by linarith [hd]) hcc'
    have hbracket : -(d / t) +
        (conditionedKernelScore ν (y + d) - conditionedKernelScore ν y) +
        (conditionedKernelScore c (y + d) - conditionedKernelScore c' y) ≤ 0 := by
      rw [hshift]
      linarith
    have hratio : 0 ≤ conditionedKernelShiftedStartDensityRatio ν c c' t d y := by
      dsimp [conditionedKernelShiftedStartDensityRatio]
      positivity
    exact mul_nonpos_of_nonneg_of_nonpos hratio hbracket

/-- The BES(3) endpoint likelihood ratio after shifting a larger start left by `d`. -/
noncomputable def conditionedKernelZeroShiftedStartDensityRatio
    (c c' t d y : ℝ) : ℝ :=
  Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
    ((y + d) / y) * (Real.sinh (c * (y + d)) / Real.sinh (c' * y))

private theorem hasDerivAt_linearShiftRatio
    {y d : ℝ} (hy : 0 < y) (hd : 0 ≤ d) :
    HasDerivAt (fun z : ℝ => (z + d) / z)
      (((y + d) / y) * (1 / (y + d) - 1 / y)) y := by
  have hnum : HasDerivAt (fun z : ℝ => z + d) 1 y := by
    convert (hasDerivAt_id y).add_const d using 1
    simp
  have hquot := hnum.div (hasDerivAt_id y) hy.ne'
  have hquot' : HasDerivAt (fun z : ℝ => (z + d) / z)
      ((1 * y - (y + d) * 1) / y ^ 2) y := hquot
  grind

private theorem conditionedKernelZeroShiftedStartDensityRatio_hasDerivAt
    {c c' t d y : ℝ} (hc' : 0 < c') (hc : 0 < c) (hy : 0 < y)
    (hd : 0 ≤ d) :
    HasDerivAt (conditionedKernelZeroShiftedStartDensityRatio c c' t d)
      (conditionedKernelZeroShiftedStartDensityRatio c c' t d y *
        (-(d / t) + (1 / (y + d) - 1 / y) +
          (conditionedKernelScore c (y + d) - conditionedKernelScore c' y))) y := by
  have hlinear : HasDerivAt (fun z : ℝ => -(d / t) * z - d ^ 2 / (2 * t))
      (-(d / t)) y := by
    convert ((hasDerivAt_id y).const_mul (-(d / t))).sub_const (d ^ 2 / (2 * t)) using 1 <;> simp
  have hexp := (Real.hasDerivAt_exp _).comp y hlinear
  have hratio := hasDerivAt_linearShiftRatio hy hd
  have hstateRatio := hasDerivAt_sinhShift_ratio hc' hc hy hd
  have hprod := (hexp.mul hratio).mul hstateRatio
  convert hprod using 1
  · ext z
    simp [conditionedKernelZeroShiftedStartDensityRatio]
  · dsimp [conditionedKernelZeroShiftedStartDensityRatio]
    ring_nf

/-- The shifted BES(3) start likelihood ratio is antitone when `d=x-x'`. -/
theorem conditionedKernelZeroShiftedStartDensityRatio_antitoneOn
    {c c' t d : ℝ} (hc' : 0 < c') (hcc' : c' ≤ c) (_ht : 0 < t)
    (hd : 0 ≤ d) (hshift : d / t = c - c') :
    AntitoneOn (conditionedKernelZeroShiftedStartDensityRatio c c' t d) (Set.Ioi 0) := by
  have hc  := lt_of_lt_of_le hc' hcc'
  have hcont : ContinuousOn (conditionedKernelZeroShiftedStartDensityRatio c c' t d)
      (Set.Ioi 0) := by
    change ContinuousOn (fun y : ℝ =>
      Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) * ((y + d) / y) *
        (Real.sinh (c * (y + d)) / Real.sinh (c' * y))) (Set.Ioi 0)
    have hExp : Continuous (fun y : ℝ =>
        Real.exp (-(d / t) * y - d ^ 2 / (2 * t))) := by fun_prop
    have hlin : ContinuousOn (fun y : ℝ => (y + d) / y) (Set.Ioi 0) := by
      apply (continuous_id.add continuous_const).continuousOn.div continuous_id.continuousOn
      intro y hy
      exact ne_of_gt (by simpa using hy)
    have hnum : Continuous (fun y : ℝ => Real.sinh (c * (y + d))) := by fun_prop
    have hden : Continuous (fun y : ℝ => Real.sinh (c' * y)) := by fun_prop
    have hratio : ContinuousOn (fun y : ℝ =>
        Real.sinh (c * (y + d)) / Real.sinh (c' * y)) (Set.Ioi 0) := by
      apply hnum.continuousOn.div hden.continuousOn
      intro y hy
      exact (Real.sinh_pos_iff.mpr (mul_pos hc' (by simpa using hy))).ne'
    exact (hExp.continuousOn.mul hlin).mul hratio
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0) hcont
  · intro y hy
    exact (conditionedKernelZeroShiftedStartDensityRatio_hasDerivAt hc' hc
      (by simpa using hy) hd).differentiableAt.differentiableWithinAt
  · intro y hy
    have hypos : 0 < y := by simpa using hy
    rw [(conditionedKernelZeroShiftedStartDensityRatio_hasDerivAt hc' hc hypos hd).deriv]
    have hlin : 1 / (y + d) - 1 / y ≤ 0 := by
      apply sub_nonpos.mpr
      exact one_div_le_one_div_of_le hypos (by linarith [hd])
    have hmixed := conditionedKernelScore_mixed_increment_upper hc' hypos
      (z := y + d) (by linarith [hd]) hcc'
    have hbracket : -(d / t) + (1 / (y + d) - 1 / y) +
        (conditionedKernelScore c (y + d) - conditionedKernelScore c' y) ≤ 0 := by
      rw [hshift]
      linarith
    have hratio : 0 ≤ conditionedKernelZeroShiftedStartDensityRatio c c' t d y := by
      dsimp [conditionedKernelZeroShiftedStartDensityRatio]
      positivity
    exact mul_nonpos_of_nonneg_of_nonpos hratio hbracket

noncomputable def conditionedKernelShiftCoefficient (ν t x x' _d : ℝ) : ℝ :=
  Real.exp (-(x ^ 2 - x' ^ 2) / (2 * t)) *
    (Real.sinh (ν * x') / Real.sinh (ν * x))

/-- The ratio of the shifted larger-start transition density to the smaller-start density is a
positive state-independent factor times the shifted likelihood ratio above. -/
theorem conditionedPositiveTransitionDensity_shifted_start_eq_ratio
    {ν t x x' d y : ℝ} (hν : 0 < ν) (ht : 0 < t) (hx' : 0 < x')
    (hxx' : x' ≤ x) (hd : 0 ≤ d) (hshift : d = x - x') (hy : 0 < y) :
    conditionedPositiveTransitionDensity ν t x (y + d) =
      conditionedKernelShiftCoefficient ν t x x' d *
        conditionedKernelShiftedStartDensityRatio ν (x / t) (x' / t) t d y *
          conditionedPositiveTransitionDensity ν t x' y := by
  have hx  := lt_of_lt_of_le hx' hxx'
  have hyD : 0 < y + d := by linarith
  have hcx  := div_pos hx ht
  have hcx'  := div_pos hx' ht
  have hKx  := (Real.sinh_pos_iff.mpr (mul_pos hν hx)).ne'
  have hKx'  := (Real.sinh_pos_iff.mpr (mul_pos hν hx')).ne'
  have hνy  := (Real.sinh_pos_iff.mpr (mul_pos hν hy)).ne'
  have hνyD  :=
    (Real.sinh_pos_iff.mpr (mul_pos hν hyD)).ne'
  have hcx'y  :=
    (Real.sinh_pos_iff.mpr (mul_pos hcx' hy)).ne'
  have hcxyd  :=
    (Real.sinh_pos_iff.mpr (mul_pos hcx hyD)).ne'
  have hExp : Real.exp (-(y + d) ^ 2 / (2 * t)) =
      Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
        Real.exp (-y ^ 2 / (2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    rw [hshift]
    field_simp [ht.ne']
    ring_nf
  rw [conditionedPositiveTransitionDensity_eq_sinh_gaussian_factor hν ht hx hyD,
    conditionedPositiveTransitionDensity_eq_sinh_gaussian_factor hν ht hx' hy]
  dsimp [conditionedKernelShiftCoefficient, conditionedKernelShiftedStartDensityRatio]
  rw [hExp]
  field_simp [hKx, hKx', hνy, hνyD, hcx'y, hcxyd]
  rw [← Real.exp_add]
  congr 1
  field_simp [ht.ne']
  ring

/-- Shifting a positive-drift kernel from a larger start left by the start difference makes its
CDF dominate the kernel from the smaller start. -/
theorem conditionedPositiveTransitionDensity_start_shift_cdf_ge
    {ν t x x' d : ℝ} (hν : 0 < ν) (ht : 0 < t) (hx' : 0 < x')
    (hxx' : x' ≤ x) (hd : 0 ≤ d) (hshift : d = x - x') (z : ℝ) :
    (∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν t x' y) ≤
      ∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν t x (y + d) := by
  have hx  := lt_of_lt_of_le hx' hxx'
  let f  := conditionedPositiveTransitionDensity ν t x'
  let g  := fun y => conditionedPositiveTransitionDensity ν t x (y + d)
  let r  := fun y =>
    conditionedKernelShiftCoefficient ν t x x' d *
      conditionedKernelShiftedStartDensityRatio ν (x / t) (x' / t) t d y
  have hf  :=
    integrable_conditionedPositiveTransitionDensity hν.le ht hx'
  have hfx  := integrable_conditionedPositiveTransitionDensity hν.le ht hx
  have hg : Integrable g (volume : Measure ℝ) :=
    (integrable_conditionedPositiveTransitionDensity hν.le ht hx).comp_add_right d
  have hunitf  :=
    conditionedPositiveTransitionDensity_integral_eq_one hν.le ht hx'
  have hunitg : ∫ y, g y = 1 :=
    (integral_add_right_eq_self _ d).trans
      (conditionedPositiveTransitionDensity_integral_eq_one hν.le ht hx)
  have hng : ∀ y, 0 ≤ g y := by
    intro y
    exact conditionedPositiveTransitionDensity_nonneg hν.le ht hx (y + d)
  have hzero : ∀ y, y ≤ 0 → f y = 0 := by
    intro y hy
    exact conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν.le ht hx' hy
  have hcoef : 0 < conditionedKernelShiftCoefficient ν t x x' d := by
    dsimp [conditionedKernelShiftCoefficient]
    positivity
  have hfactor : ∀ y, 0 < y → g y = r y * f y := by
    intro y hy
    exact conditionedPositiveTransitionDensity_shifted_start_eq_ratio hν ht hx'
      hxx' hd hshift hy
  have hrpos : ∀ y, 0 < y → 0 < r y := by
    intro y hy
    dsimp [r]
    apply mul_pos hcoef
    dsimp [conditionedKernelShiftedStartDensityRatio]
    positivity
  have hratio : AntitoneOn r (Set.Ioi 0) := by
    intro y₁ hy₁ y₂ hy₂ hy₁₂
    dsimp [r]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hcoef)
    exact conditionedKernelShiftedStartDensityRatio_antitoneOn hν
      (div_pos hx' ht) (div_le_div_of_nonneg_right hxx' ht.le)
      ht hd (by rw [hshift]; field_simp [ht.ne']) hy₁ hy₂ hy₁₂
  have hcomp := integral_Iic_ge_of_shiftedAntitoneDensityRatio hf hg hng hzero
    hunitf hunitg hfactor hrpos hratio z
  simpa [f, g] using hcomp

/-- Under the shift `d/t = b-a`, the larger-drift transition law shifted left by `d`
has CDF at least the smaller-drift transition law. -/
theorem conditionedPositiveTransitionDensity_shifted_drift_cdf_ge
    {a b t x d : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t)
    (hx : 0 < x) (hd : 0 ≤ d) (hshift : d / t = b - a) (z : ℝ) :
    (∫ y in Set.Iic z, conditionedPositiveTransitionDensity a t x y) ≤
      ∫ y in Set.Iic z, conditionedPositiveTransitionDensity b t x (y + d) := by
  have hb  := lt_of_lt_of_le ha hab
  let f  := conditionedPositiveTransitionDensity a t x
  let g  := fun y => conditionedPositiveTransitionDensity b t x (y + d)
  let r  := fun y =>
    conditionedPositiveTransitionDensity b t x (y + d) /
      conditionedPositiveTransitionDensity a t x y
  have hf  :=
    integrable_conditionedPositiveTransitionDensity ha.le ht hx
  have hg : Integrable g (volume : Measure ℝ) :=
    (integrable_conditionedPositiveTransitionDensity hb.le ht hx).comp_add_right d
  have hunitf  :=
    conditionedPositiveTransitionDensity_integral_eq_one ha.le ht hx
  have hunitg : ∫ y, g y = 1 :=
    (integral_add_right_eq_self _ d).trans
      (conditionedPositiveTransitionDensity_integral_eq_one hb.le ht hx)
  have hng : ∀ y, 0 ≤ g y := by
    intro y
    exact conditionedPositiveTransitionDensity_nonneg hb.le ht hx (y + d)
  have hzero : ∀ y, y ≤ 0 → f y = 0 := by
    intro y hy
    exact conditionedPositiveTransitionDensity_eq_zero_of_nonpos ha.le ht hx hy
  have hfp : ∀ y, 0 < y → 0 < f y := by
    intro y hy
    exact conditionedPositiveTransitionDensity_pos ha.le ht hx hy
  have hgp : ∀ y, 0 < y → 0 < g y := by
    intro y hy
    exact conditionedPositiveTransitionDensity_pos hb.le ht hx (by linarith [hy, hd])
  have hfactor : ∀ y, 0 < y → g y = r y * f y := by
    intro y hy
    simpa [r, f, g] using
      (div_mul_cancel₀ (conditionedPositiveTransitionDensity b t x (y + d))
        (ne_of_gt (hfp y hy))).symm
  have hrpos : ∀ y, 0 < y → 0 < r y := by
    intro y hy
    exact div_pos (hgp y hy) (hfp y hy)
  have hratio : AntitoneOn r (Set.Ioi 0) := by
    simpa [r] using conditionedPositiveTransitionDensity_shifted_ratio_antitoneOn
      ha hab ht hx hd hshift
  have hcomp := integral_Iic_ge_of_shiftedAntitoneDensityRatio hf hg hng hzero
    hunitf hunitg hfactor hrpos hratio z
  simpa [f, g] using hcomp

/-- State-independent prefactor for shifting a zero-drift transition from a larger start. -/
noncomputable def conditionedKernelZeroShiftCoefficient (t x x' _d : ℝ) : ℝ :=
  Real.exp (-(x ^ 2 - x' ^ 2) / (2 * t)) * (x' / x)

/-- The shifted BES(3) transition density is its smaller-start density times the explicit
state-independent coefficient and zero-drift shifted likelihood ratio. -/
theorem conditionedPositiveTransitionDensity_zero_shifted_start_eq_ratio
    {t x x' d y : ℝ} (ht : 0 < t) (hx' : 0 < x') (hxx' : x' ≤ x)
    (hd : 0 ≤ d) (hshift : d = x - x') (hy : 0 < y) :
    conditionedPositiveTransitionDensity 0 t x (y + d) =
      conditionedKernelZeroShiftCoefficient t x x' d *
        conditionedKernelZeroShiftedStartDensityRatio (x / t) (x' / t) t d y *
          conditionedPositiveTransitionDensity 0 t x' y := by
  have hx  := lt_of_lt_of_le hx' hxx'
  have hyD : 0 < y + d := by linarith
  have hcx  := div_pos hx ht
  have hcx'  := div_pos hx' ht
  have hroot : Real.sqrt (2 * Real.pi * t) ≠ 0 := by positivity
  have hExpY : Real.exp (-(y + d) ^ 2 / (2 * t)) =
      Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
        Real.exp (-y ^ 2 / (2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    rw [hshift]
    field_simp [ht.ne']
    ring
  have hExpX : Real.exp (-(x ^ 2 - x' ^ 2) / (2 * t)) *
      Real.exp (-x' ^ 2 / (2 * t)) = Real.exp (-x ^ 2 / (2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp [ht.ne']
    ring
  rw [conditionedPositiveTransitionDensity_zero_eq_sinh_gaussian_factor
      ht hx hyD,
    conditionedPositiveTransitionDensity_zero_eq_sinh_gaussian_factor ht hx' hy]
  dsimp [conditionedKernelZeroShiftCoefficient,
    conditionedKernelZeroShiftedStartDensityRatio]
  have hyne  := ne_of_gt hy
  have hyDne  := ne_of_gt hyD
  have hs1  :=
    (Real.sinh_pos_iff.mpr (mul_pos hcx hyD)).ne'
  have hs2  :=
    (Real.sinh_pos_iff.mpr (mul_pos hcx' hy)).ne'
  grind

/-- The zero-drift shifted-start density comparison, including its mass to the left of zero. -/
theorem conditionedPositiveTransitionDensity_zero_start_shift_cdf_ge
    {t x x' d : ℝ} (ht : 0 < t) (hx' : 0 < x') (hxx' : x' ≤ x)
    (hd : 0 ≤ d) (hshift : d = x - x') (z : ℝ) :
    (∫ y in Set.Iic z, conditionedPositiveTransitionDensity 0 t x' y) ≤
      ∫ y in Set.Iic z, conditionedPositiveTransitionDensity 0 t x (y + d) := by
  have hx  := lt_of_lt_of_le hx' hxx'
  let f  := conditionedPositiveTransitionDensity 0 t x'
  let g  := fun y => conditionedPositiveTransitionDensity 0 t x (y + d)
  let r  := fun y =>
    conditionedKernelZeroShiftCoefficient t x x' d *
      conditionedKernelZeroShiftedStartDensityRatio (x / t) (x' / t) t d y
  have hf : Integrable f (volume : Measure ℝ) :=
    integrable_conditionedPositiveTransitionDensity (by norm_num) ht hx'
  have hfx : Integrable (conditionedPositiveTransitionDensity 0 t x)
      (volume : Measure ℝ) := integrable_conditionedPositiveTransitionDensity (by norm_num) ht hx
  have hg : Integrable g (volume : Measure ℝ) :=
    (integrable_conditionedPositiveTransitionDensity (by norm_num) ht hx).comp_add_right d
  have hunitf : ∫ y, f y = 1 :=
    conditionedPositiveTransitionDensity_integral_eq_one (by norm_num) ht hx'
  have hunitg : ∫ y, g y = 1 :=
    (integral_add_right_eq_self _ d).trans
      (conditionedPositiveTransitionDensity_integral_eq_one (by norm_num) ht hx)
  have hng : ∀ y, 0 ≤ g y := by
    intro y
    exact conditionedPositiveTransitionDensity_nonneg (by norm_num) ht hx (y + d)
  have hzero : ∀ y, y ≤ 0 → f y = 0 := by
    intro y hy
    exact conditionedPositiveTransitionDensity_eq_zero_of_nonpos (by norm_num) ht hx' hy
  have hcoef : 0 < conditionedKernelZeroShiftCoefficient t x x' d := by
    dsimp [conditionedKernelZeroShiftCoefficient]
    exact mul_pos (Real.exp_pos _) (div_pos hx' hx)
  have hfactor : ∀ y, 0 < y → g y = r y * f y := by
    intro y hy
    exact conditionedPositiveTransitionDensity_zero_shifted_start_eq_ratio ht hx'
      hxx' hd hshift hy
  have hrpos : ∀ y, 0 < y → 0 < r y := by
    intro y hy
    dsimp [r]
    apply mul_pos hcoef
    dsimp [conditionedKernelZeroShiftedStartDensityRatio]
    positivity
  have hratio : AntitoneOn r (Set.Ioi 0) := by
    intro y₁ hy₁ y₂ hy₂ hy₁₂
    dsimp [r]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hcoef)
    exact conditionedKernelZeroShiftedStartDensityRatio_antitoneOn
      (div_pos hx' ht) (div_le_div_of_nonneg_right hxx' ht.le) ht hd
      (by rw [hshift]; field_simp [ht.ne']) hy₁ hy₂ hy₁₂
  have hcomp := integral_Iic_ge_of_shiftedAntitoneDensityRatio hf hg hng hzero
    hunitf hunitg hfactor hrpos hratio z
  simpa [f, g] using hcomp

/-- The common-uniform upper start bound for positive-drift conditioned transitions:
increasing the initial state by `d` raises the endpoint quantile by at most `d`. -/
theorem conditionedPositiveTransitionQuantile_start_add
    {ν t x x' u : ℝ} (hν : 0 < ν) (ht : 0 < t) (hx' : 0 < x')
    (hxx' : x' ≤ x) (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x')) u + (x - x') := by
  have hx := hx'.trans_le hxx'
  let := isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x' hν.le ht hx'
  let := isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x hν.le ht hx
  apply cdfGeneralizedQuantile_le_add_of_cdf_le_shift hu hu1
  intro z
  rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hν.le ht hx',
    conditionedPositiveTransitionMeasure_cdf_eq_integral hν.le ht hx,
    ← integral_Iic_add_shift (x - x') z]
  exact conditionedPositiveTransitionDensity_start_shift_cdf_ge hν ht hx' hxx'
    (sub_nonneg.mpr hxx') rfl z

/-- The common-uniform upper start bound for the zero-drift BES(3) transition: increasing the
initial state by `d` raises the endpoint quantile by at most `d`. -/
theorem conditionedPositiveTransitionQuantile_start_add_zero
    {t x x' u : ℝ} (ht : 0 < t) (hx' : 0 < x')
    (hxx' : x' ≤ x) (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure 0 t x)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure 0 t x')) u + (x - x') := by
  have hx := hx'.trans_le hxx'
  let := isProbabilityMeasure_conditionedPositiveTransitionMeasure 0 t x' le_rfl ht hx'
  let := isProbabilityMeasure_conditionedPositiveTransitionMeasure 0 t x le_rfl ht hx
  apply cdfGeneralizedQuantile_le_add_of_cdf_le_shift hu hu1
  intro z
  rw [conditionedPositiveTransitionMeasure_cdf_eq_integral le_rfl ht hx',
    conditionedPositiveTransitionMeasure_cdf_eq_integral le_rfl ht hx,
    ← integral_Iic_add_shift (x - x') z]
  exact conditionedPositiveTransitionDensity_zero_start_shift_cdf_ge ht hx' hxx'
    (sub_nonneg.mpr hxx') rfl z

/-- The common-uniform upper drift bound for positive conditioned transitions. Increasing drift
by `b-a` raises the endpoint quantile by at most `(b-a)t`. -/
theorem conditionedPositiveTransitionQuantile_drift_add
    {a b t x u : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) (hx : 0 < x)
    (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure b t x)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure a t x)) u +
          (b - a) * t := by
  have hb := ha.trans_le hab
  let := isProbabilityMeasure_conditionedPositiveTransitionMeasure a t x ha.le ht hx
  let := isProbabilityMeasure_conditionedPositiveTransitionMeasure b t x hb.le ht hx
  apply cdfGeneralizedQuantile_le_add_of_cdf_le_shift hu hu1
  intro z
  rw [conditionedPositiveTransitionMeasure_cdf_eq_integral ha.le ht hx,
    conditionedPositiveTransitionMeasure_cdf_eq_integral hb.le ht hx,
    ← integral_Iic_add_shift ((b - a) * t) z]
  exact conditionedPositiveTransitionDensity_shifted_drift_cdf_ge ha hab ht hx
    (mul_nonneg (sub_nonneg.mpr hab) ht.le) (by field_simp [ht.ne']) z

/-- The common-uniform upper drift bound from the zero-drift BES(3) endpoint. Increasing the
positive drift by `b` raises the endpoint quantile by at most `b * t`. -/
theorem conditionedPositiveTransitionQuantile_drift_add_zero
    {b t x u : ℝ} (hb : 0 < b) (ht : 0 < t) (hx : 0 < x)
    (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure b t x)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure 0 t x)) u + b * t := by
  let := isProbabilityMeasure_conditionedPositiveTransitionMeasure 0 t x le_rfl ht hx
  let := isProbabilityMeasure_conditionedPositiveTransitionMeasure b t x hb.le ht hx
  apply cdfGeneralizedQuantile_le_add_of_cdf_le_shift hu hu1
  intro z
  rw [conditionedPositiveTransitionMeasure_cdf_eq_integral le_rfl ht hx,
    conditionedPositiveTransitionMeasure_cdf_eq_integral hb.le ht hx,
    ← integral_Iic_add_shift (b * t) z]
  exact conditionedPositiveTransitionDensity_shifted_zero_cdf_ge hb ht hx
    (mul_nonneg hb.le ht.le) (by field_simp [ht.ne']) z

end DOZZ.Proofs

end
