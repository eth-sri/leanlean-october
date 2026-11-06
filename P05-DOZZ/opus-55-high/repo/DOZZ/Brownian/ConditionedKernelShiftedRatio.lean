/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelScoreParameter
public import DOZZ.Brownian.ConditionedKernelParameterRatio
public import DOZZ.Brownian.ConditionedKernelCDFOrder
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import DOZZ.Brownian.ConditionedKernelStartRatio

/-!
# Shifted likelihood ratio for conditioned kernels

The upper quantile bounds used to couple conditioned Brownian kernels compare a shifted endpoint
density with an unshifted one. This module proves the required antitonicity of its state-dependent
ratio for strictly positive drift parameters.
-/

@[expose] public section

open MeasureTheory Topology Set

namespace DOZZ.Proofs

/-- The endpoint-dependent part of the ratio between a shifted `(b,c)` kernel and an unshifted
`(a,c)` kernel. The omitted factor is positive and independent of the endpoint. -/
noncomputable def conditionedKernelShiftedDensityRatio
    (a b c t d y : ℝ) : ℝ :=
  Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
    (Real.sinh (b * (y + d)) / Real.sinh (a * y)) *
      (Real.sinh (c * (y + d)) / Real.sinh (c * y))

private theorem shiftedRatio_conditionedH_sinh
    {ν x : ℝ} (hν : 0 < ν) :
    conditionedH ν x = 2 * Real.exp (-ν * x) * Real.sinh (ν * x) := by
  simp only [conditionedH, ite_eq_right (ne_of_gt hν)]
  have h := DOZZ.Proofs.one_sub_exp_neg_two_mul_eq_two_exp_neg_mul_sinh (ν * x)
  grind

/-- For strictly positive drift, the transition density's endpoint dependence is a fixed positive
factor times its Gaussian and two hyperbolic-sine factors. -/
theorem conditionedPositiveTransitionDensity_eq_sinh_gaussian_factor
    {ν t x y : ℝ} (hν : 0 < ν) (ht : 0 < t) (hx : 0 < x) (hy : 0 < y) :
    conditionedPositiveTransitionDensity ν t x y =
      (2 * Real.exp (-ν ^ 2 * t / 2 - x ^ 2 / (2 * t)) /
        (Real.sqrt (2 * Real.pi * t) * Real.sinh (ν * x))) *
        (Real.exp (-y ^ 2 / (2 * t)) * Real.sinh (ν * y) * Real.sinh (x * y / t)) := by
  have hHνx := shiftedRatio_conditionedH_sinh (x := x) hν
  have hsinhX :=
    Real.sinh_pos_iff.mpr (div_pos (mul_pos hx hy) ht)
  have hsinhνx :=
    Real.sinh_pos_iff.mpr (mul_pos hν hx)
  have hroot : 0 < Real.sqrt (2 * Real.pi * t) := by positivity
  simp [conditionedPositiveTransitionDensity, hν.le, ht, hx, hy,
    (DOZZ.Proofs.brownianHeatDensity_sub_factor ht (x := x) (y := y)), (shiftedRatio_conditionedH_sinh (x := y) hν), hHνx]
  field_simp [hroot.ne', hsinhνx.ne']
  conv_lhs => rw [← Real.exp_add, ← Real.exp_add]
  conv_rhs => rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_injective
  field_simp [ht.ne']
  ring_nf

/-- The shifted ratio proved monotone above is exactly the state-dependent part of the ratio of
the positive-drift transition densities. -/
theorem conditionedPositiveTransitionDensity_shifted_eq_ratio
    {a b t x d y : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t)
    (hx : 0 < x) (hd : 0 ≤ d) (hy : 0 < y) :
    conditionedPositiveTransitionDensity b t x (y + d) =
      (Real.exp (-((b ^ 2 - a ^ 2) * t / 2)) *
        (Real.sinh (a * x) / Real.sinh (b * x))) *
        conditionedKernelShiftedDensityRatio a b (x / t) t d y *
          conditionedPositiveTransitionDensity a t x y := by
  have hb := lt_of_lt_of_le ha hab
  have hyD : 0 < y + d := by linarith
  have hca :=
    (Real.sinh_pos_iff.mpr (mul_pos ha hx)).ne'
  have hcb :=
    (Real.sinh_pos_iff.mpr (mul_pos hb hx)).ne'
  have hcy :=
    (Real.sinh_pos_iff.mpr (mul_pos (div_pos hx ht) hy)).ne'
  have hcbD :=
    (Real.sinh_pos_iff.mpr (mul_pos hb hyD)).ne'
  have hcaY :=
    (Real.sinh_pos_iff.mpr (mul_pos ha hy)).ne'
  have hcoef :
      2 * Real.exp (-b ^ 2 * t / 2 - x ^ 2 / (2 * t)) /
          (Real.sqrt (2 * Real.pi * t) * Real.sinh (b * x)) =
      Real.exp (-((b ^ 2 - a ^ 2) * t / 2)) *
        (Real.sinh (a * x) / Real.sinh (b * x)) *
          (2 * Real.exp (-a ^ 2 * t / 2 - x ^ 2 / (2 * t)) /
            (Real.sqrt (2 * Real.pi * t) * Real.sinh (a * x))) := by
    field_simp [hca, hcb]
    rw [← Real.exp_add]
    grind
  have hExp : Real.exp (-(y + d) ^ 2 / (2 * t)) =
      Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
        Real.exp (-y ^ 2 / (2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp [ht.ne']
    ring_nf
  rw [conditionedPositiveTransitionDensity_eq_sinh_gaussian_factor hb ht hx hyD,
    conditionedPositiveTransitionDensity_eq_sinh_gaussian_factor ha ht hx hy, hcoef]
  dsimp [conditionedKernelShiftedDensityRatio]
  rw [hExp]
  field_simp [hca, hcb, hcy, hcbD, hcaY]

theorem hasDerivAt_sinhShift_ratio
    {a b y d : ℝ} (ha : 0 < a) (hb : 0 < b) (hy : 0 < y) (hd : 0 ≤ d) :
    HasDerivAt (fun z : ℝ => Real.sinh (b * (z + d)) / Real.sinh (a * z))
      ((Real.sinh (b * (y + d)) / Real.sinh (a * y)) *
        (conditionedKernelScore b (y + d) - conditionedKernelScore a y)) y := by
  have hnumArg : HasDerivAt (fun z : ℝ => b * (z + d)) b y := by
    convert ((hasDerivAt_id y).add_const d).const_mul b using 1 <;> simp
  have hdenArg : HasDerivAt (fun z : ℝ => a * z) a y := by
    convert (hasDerivAt_id y).const_mul a using 1 <;> simp
  have hdenPos := Real.sinh_pos_iff.mpr (mul_pos ha hy)
  have hnumPos :=
    Real.sinh_pos_iff.mpr (mul_pos hb (by linarith))
  have hquot := ((Real.hasDerivAt_sinh _).comp y hnumArg).div ((Real.hasDerivAt_sinh _).comp y hdenArg) hdenPos.ne'
  have hquot' : HasDerivAt
      (fun z : ℝ => Real.sinh (b * (z + d)) / Real.sinh (a * z))
      ((Real.cosh (b * (y + d)) * b * Real.sinh (a * y) -
          Real.sinh (b * (y + d)) * (Real.cosh (a * y) * a)) /
        Real.sinh (a * y) ^ 2) y := by
    assumption
  have halgebra :
      (Real.cosh (b * (y + d)) * b * Real.sinh (a * y) -
          Real.sinh (b * (y + d)) * (Real.cosh (a * y) * a)) /
        Real.sinh (a * y) ^ 2 =
      (Real.sinh (b * (y + d)) / Real.sinh (a * y)) *
        (conditionedKernelScore b (y + d) - conditionedKernelScore a y) := by
    dsimp [conditionedKernelScore]
    field_simp
  simp_all

/-- The shifted kernel likelihood ratio has logarithmic derivative equal to the sum of the
Gaussian shift and two hyperbolic score increments. -/
theorem hasDerivAt_conditionedKernelShiftedDensityRatio
    {a b c t d y : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hy : 0 < y) (hd : 0 ≤ d) :
    HasDerivAt (conditionedKernelShiftedDensityRatio a b c t d)
      (conditionedKernelShiftedDensityRatio a b c t d y *
        (-(d / t) + (conditionedKernelScore b (y + d) - conditionedKernelScore a y) +
          (conditionedKernelScore c (y + d) - conditionedKernelScore c y))) y := by
  have hlinear : HasDerivAt (fun z => -(d / t) * z - d ^ 2 / (2 * t))
      (-(d / t)) y := by
    convert ((hasDerivAt_id y).const_mul (-(d / t))).sub_const (d ^ 2 / (2 * t)) using 1 <;> simp
  have hr2 := hasDerivAt_sinhShift_ratio hc hc hy hd
  have hprod := (((Real.hasDerivAt_exp _).comp y hlinear).mul (hasDerivAt_sinhShift_ratio ha hb hy hd)).mul hr2
  change HasDerivAt (fun z =>
    Real.exp _ *
      (Real.sinh _ / Real.sinh _) *
        (Real.sinh _ / Real.sinh _)) _ y
  convert hprod using 1
  · rfl
  · dsimp [conditionedKernelShiftedDensityRatio]
    ring_nf

/-- Under the shift `d/t=b-a`, the shifted likelihood ratio is nonincreasing in the
endpoint. This is the analytic upper-bound input for the corresponding quantile comparison. -/
theorem conditionedKernelShiftedDensityRatio_antitoneOn
    {a b c t d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c)
    (_ht : 0 < t) (hd : 0 ≤ d) (hshift : d / t = b - a) :
    AntitoneOn (conditionedKernelShiftedDensityRatio a b c t d) (Set.Ioi 0) := by
  have hb := lt_of_lt_of_le ha hab
  have hcont : ContinuousOn (conditionedKernelShiftedDensityRatio a b c t d) (Set.Ioi 0) := by
    change ContinuousOn (fun y =>
      Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
        (Real.sinh (b * (y + d)) / Real.sinh (a * y)) *
          (Real.sinh (c * (y + d)) / Real.sinh (c * y))) (Set.Ioi 0)
    have hExp : Continuous (fun y =>
        Real.exp (-(d / t) * y - d ^ 2 / (2 * t))) := by fun_prop
    have hn1 : Continuous (fun y => Real.sinh (b * (y + d))) := by fun_prop
    have hd1 : Continuous (fun y => Real.sinh (a * y)) := by fun_prop
    have hr1 : ContinuousOn (fun y =>
        Real.sinh (b * (y + d)) / Real.sinh (a * y)) (Set.Ioi 0) := by
      apply hn1.continuousOn.div hd1.continuousOn
      aesop
    have hn2 : Continuous (fun y => Real.sinh (c * (y + d))) := by fun_prop
    have hd2 : Continuous (fun y => Real.sinh (c * y)) := by fun_prop
    have hr2 : ContinuousOn (fun y =>
        Real.sinh (c * (y + d)) / Real.sinh (c * y)) (Set.Ioi 0) := by
      apply hn2.continuousOn.div hd2.continuousOn
      aesop
    fun_prop
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0) hcont
  · intro y hy
    have hypos : 0 < y := by simp_all
    exact (hasDerivAt_conditionedKernelShiftedDensityRatio ha hb hc hypos hd).differentiableAt.differentiableWithinAt
  · intro y hy
    have hypos : 0 < y := by simp_all
    rw [(hasDerivAt_conditionedKernelShiftedDensityRatio ha hb hc hypos hd).deriv]
    have hparam := conditionedKernelScore_mixed_increment_upper ha hypos
      (z := y + d) (by linarith) hab
    have hstate : conditionedKernelScore c (y + d) - conditionedKernelScore c y ≤ 0 := by
      exact sub_nonpos.mpr (((conditionedKernelScore_strictAntiOn_state hc).antitoneOn) (Set.mem_Ioi.mpr hypos)
        (Set.mem_Ioi.mpr (by linarith)) (by linarith))
    have hbracket :
        -(d / t) + (conditionedKernelScore b (y + d) - conditionedKernelScore a y) +
          (conditionedKernelScore c (y + d) - conditionedKernelScore c y) ≤ 0 := by
      linarith
    have hratio : 0 ≤ conditionedKernelShiftedDensityRatio a b c t d y := by
      dsimp [conditionedKernelShiftedDensityRatio]
      positivity
    nlinarith

/-- The likelihood ratio of the actual positive-drift transition densities under the shift
`d/t = b-a` is nonincreasing in the endpoint. This is the upper single-crossing input for
stochastic order. -/
theorem conditionedPositiveTransitionDensity_shifted_ratio_antitoneOn
    {a b t x d : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t)
    (hx : 0 < x) (hd : 0 ≤ d) (hshift : d / t = b - a) :
    AntitoneOn
      (fun y => conditionedPositiveTransitionDensity b t x (y + d) /
        conditionedPositiveTransitionDensity a t x y) (Set.Ioi 0) := by
  have hb := lt_of_lt_of_le ha hab
  let C := Real.exp (-((b ^ 2 - a ^ 2) * t / 2)) *
    (Real.sinh (a * x) / Real.sinh (b * x))
  have hC : 0 < C := by
    positivity
  have hR := conditionedKernelShiftedDensityRatio_antitoneOn
    ha hab (div_pos hx ht) ht hd hshift
  have hdenPos (y : ℝ) (hy : 0 < y) :
      0 < conditionedPositiveTransitionDensity a t x y := by
    rw [conditionedPositiveTransitionDensity_eq_sinh_gaussian_factor ha ht hx hy]
    positivity
  have hfactor (y : ℝ) (hy : 0 < y) :
      conditionedPositiveTransitionDensity b t x (y + d) /
        conditionedPositiveTransitionDensity a t x y =
      C * conditionedKernelShiftedDensityRatio a b (x / t) t d y := by
    rw [conditionedPositiveTransitionDensity_shifted_eq_ratio ha hab ht hx hd hy]
    grind
  intro y₁ hy₁ y₂ hy₂ hy₁₂
  have hy₁' : 0 < y₁ := by assumption
  have hy₂' : 0 < y₂ := by assumption
  change conditionedPositiveTransitionDensity b t x _ /
      conditionedPositiveTransitionDensity a t x y₂ ≤
    conditionedPositiveTransitionDensity b t x _ /
      conditionedPositiveTransitionDensity a t x y₁
  rw [hfactor y₂ hy₂', hfactor y₁ hy₁']
  exact mul_le_mul_of_nonneg_left (hR hy₁ hy₂ hy₁₂) (le_of_lt hC)

/-- Endpoint-dependent likelihood ratio for shifting a positive-drift transition density against
the zero-drift BES(3) kernel. The factor `sinh (b (y+d)) / y` is the continuous zero-parameter
limit of the first hyperbolic quotient in `conditionedKernelShiftedDensityRatio`. -/
noncomputable def conditionedKernelShiftedZeroDensityRatio
    (b c t d y : ℝ) : ℝ :=
  Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
    (Real.sinh (b * (y + d)) / y) *
      (Real.sinh (c * (y + d)) / Real.sinh (c * y))

private theorem hasDerivAt_sinhShift_div_state
    {b y d : ℝ} (hb : 0 < b) (hy : 0 < y) (hd : 0 ≤ d) :
    HasDerivAt (fun z : ℝ => Real.sinh (b * (z + d)) / z)
      ((Real.sinh (b * (y + d)) / y) *
        (conditionedKernelScore b (y + d) - 1 / y)) y := by
  have harg : HasDerivAt (fun z : ℝ => b * (z + d)) b y := by
    convert ((hasDerivAt_id y).add_const d).const_mul b using 1 <;> simp
  have hquot := ((Real.hasDerivAt_sinh _).comp y harg).div (hasDerivAt_id y) hy.ne'
  have hquot' : HasDerivAt (fun z : ℝ => Real.sinh (b * (z + d)) / z)
      ((Real.cosh (b * (y + d)) * b * y - Real.sinh (b * (y + d))) / y ^ 2) y := by
    aesop
  have hden : Real.sinh (b * (y + d)) ≠ 0 :=
    by positivity
  have halg :
      (Real.cosh (b * (y + d)) * b * y - Real.sinh (b * (y + d))) / y ^ 2 =
        (Real.sinh (b * (y + d)) / y) *
          (conditionedKernelScore b (y + d) - 1 / y) := by
    dsimp [conditionedKernelScore]
    field_simp
  simp_all

private theorem hasDerivAt_shiftedExpFactor
    {t d y : ℝ} (_ht : 0 < t) :
    HasDerivAt (fun z : ℝ => Real.exp (-(d / t) * z - d ^ 2 / (2 * t)))
      (Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) * (-(d / t))) y := by
  have harg : HasDerivAt (fun z => -(d / t) * z - d ^ 2 / (2 * t))
      (-(d / t)) y := by
    convert ((hasDerivAt_id y).const_mul (-(d / t))).add_const (-(d ^ 2 / (2 * t))) using 1
    · rfl
    · ring
  exact (Real.hasDerivAt_exp _).comp y harg

/-- The shifted zero-drift likelihood ratio has logarithmic derivative equal to its shifted-score
difference. -/
theorem hasDerivAt_conditionedKernelShiftedZeroDensityRatio
    {b c t d y : ℝ} (hb : 0 < b) (hc : 0 < c) (ht : 0 < t)
    (hd : 0 ≤ d) (hy : 0 < y) :
    HasDerivAt (conditionedKernelShiftedZeroDensityRatio b c t d)
      (conditionedKernelShiftedZeroDensityRatio b c t d y *
        (-(d / t) + (conditionedKernelScore b (y + d) - 1 / y) +
          (conditionedKernelScore c (y + d) - conditionedKernelScore c y))) y := by
  have hH := hasDerivAt_sinhShift_ratio hc hc hy hd
  have hprod := ((hasDerivAt_shiftedExpFactor ht (d := d)).mul (hasDerivAt_sinhShift_div_state hb hy hd)).mul hH
  change HasDerivAt (fun z =>
    (Real.exp _ *
      (Real.sinh _ / z)) *
        (Real.sinh _ / Real.sinh _)) _ y
  convert hprod using 1
  · dsimp [conditionedKernelShiftedZeroDensityRatio]
    ring_nf

/-- The zero-drift endpoint of the shifted-kernel score estimate: when `d/t=b`, this likelihood
ratio is antitone in the endpoint. -/
theorem conditionedKernelShiftedZeroDensityRatio_antitoneOn
    {b c t d : ℝ} (hb : 0 < b) (hc : 0 < c) (ht : 0 < t)
    (hd : 0 ≤ d) (hdt : d / t = b) :
    AntitoneOn (conditionedKernelShiftedZeroDensityRatio b c t d) (Set.Ioi 0) := by
  have hcont : ContinuousOn (conditionedKernelShiftedZeroDensityRatio b c t d)
      (Set.Ioi 0) := by
    change ContinuousOn (fun y =>
      Real.exp _ *
        (Real.sinh _ / y) *
          (Real.sinh _ / Real.sinh _)) (Set.Ioi 0)
    have hE : Continuous (fun y => Real.exp (-(d / t) * y - d ^ 2 / (2 * t))) := by
      fun_prop
    have hG : ContinuousOn (fun y => Real.sinh (b * (y + d)) / y) (Set.Ioi 0) := by
      apply (Real.continuous_sinh.comp
        (continuous_const.mul (continuous_id.add continuous_const))).continuousOn.div
        continuousOn_id
      aesop
    have hH : ContinuousOn (fun y =>
        Real.sinh (c * (y + d)) / Real.sinh (c * y)) (Set.Ioi 0) := by
      apply (Real.continuous_sinh.comp
        (continuous_const.mul (continuous_id.add continuous_const))).continuousOn.div
        (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).continuousOn
      aesop
    fun_prop
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) hcont ?_ ?_
  · intro y hy
    have hy' : 0 < y := by simp_all
    exact (hasDerivAt_conditionedKernelShiftedZeroDensityRatio hb hc ht hd hy').differentiableAt.differentiableWithinAt
  · intro y hy
    have hy' : 0 < y := by simp_all
    rw [(hasDerivAt_conditionedKernelShiftedZeroDensityRatio hb hc ht hd hy').deriv]
    have hyD : 0 < y + d := by linarith
    have hscoreStateB : conditionedKernelScore b (y + d) ≤ conditionedKernelScore b y := by
      have hanti := (conditionedKernelScore_strictAntiOn_state hb).antitoneOn
      aesop
    have hscoreB := conditionedKernelScore_zero_increment_bounds hb hy'
    have hscoreStateC : conditionedKernelScore c (y + d) ≤ conditionedKernelScore c y := by
      have hanti := (conditionedKernelScore_strictAntiOn_state hc).antitoneOn
      aesop
    have hratio : 0 < conditionedKernelShiftedZeroDensityRatio b c t d y := by
      dsimp [conditionedKernelShiftedZeroDensityRatio]
      positivity
    nlinarith

theorem conditionedPositiveTransitionDensity_zero_eq_sinh_gaussian_factor
    {t x y : ℝ} (ht : 0 < t) (hx : 0 < x) (hy : 0 < y) :
    conditionedPositiveTransitionDensity 0 t x y =
      (2 * Real.exp (-x ^ 2 / (2 * t)) /
        (Real.sqrt (2 * Real.pi * t) * x)) *
        (Real.exp (-y ^ 2 / (2 * t)) * y * Real.sinh (x / t * y)) := by
  have hsqrt : Real.sqrt (2 * Real.pi * t) ≠ 0 := by positivity
  simp [conditionedPositiveTransitionDensity, conditionedH, ht, hx, hy]
  rw [(DOZZ.Proofs.brownianHeatDensity_sub_factor ht (x := x) (y := y))]
  have hexp : Real.exp (-(x ^ 2 + y ^ 2) / (2 * t)) =
      Real.exp (-x ^ 2 / (2 * t)) * Real.exp (-y ^ 2 / (2 * t)) := by
    rw [← Real.exp_add]
    ring
  grind

/-- The actual positive-drift transition kernel shifted by `d` is the zero-drift kernel times the
zero-endpoint shifted likelihood ratio, up to a positive factor independent of `y`. -/
theorem conditionedPositiveTransitionDensity_shifted_from_zero_eq_ratio
    {b t x d y : ℝ} (hb : 0 < b) (ht : 0 < t) (hx : 0 < x)
    (hd : 0 ≤ d) (hy : 0 < y) :
    conditionedPositiveTransitionDensity b t x (y + d) =
      (Real.exp (-b ^ 2 * t / 2) * (x / Real.sinh (b * x))) *
        conditionedKernelShiftedZeroDensityRatio b (x / t) t d y *
          conditionedPositiveTransitionDensity 0 t x y := by
  have hc := div_pos hx ht
  have hyD : 0 < y + d := by linarith
  have hpos := conditionedPositiveTransitionDensity_eq_sinh_gaussian_factor
    hb ht hx hyD
  have hsqrt : Real.sqrt (2 * Real.pi * t) ≠ 0 := by positivity
  have hsinhX :=
    (Real.sinh_pos_iff.mpr (mul_pos hb hx)).ne'
  have hsinhY :=
    (Real.sinh_pos_iff.mpr (mul_pos hc hy)).ne'
  have hsinhYD :=
    (Real.sinh_pos_iff.mpr (mul_pos hc hyD)).ne'
  have hExp : Real.exp (-(y + d) ^ 2 / (2 * t)) =
      Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
        Real.exp (-y ^ 2 / (2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp [ht.ne']
    ring_nf
  let Cb := 2 * Real.exp (-b ^ 2 * t / 2 - x ^ 2 / (2 * t)) /
      (Real.sqrt (2 * Real.pi * t) * Real.sinh (b * x))
  let C0 := 2 * Real.exp (-x ^ 2 / (2 * t)) /
      (Real.sqrt (2 * Real.pi * t) * x)
  let K := Real.exp (-b ^ 2 * t / 2) * (x / Real.sinh (b * x))
  have hC : Cb = K * C0 := by
    dsimp [Cb, C0, K]
    field_simp [hsqrt, hsinhX, hx.ne', ht.ne']
    rw [← Real.exp_add]
    congr 1
    field_simp [ht.ne']
    ring_nf
  have hCexplicit :
      2 * Real.exp (-b ^ 2 * t / 2 - x ^ 2 / (2 * t)) /
          (Real.sqrt (2 * Real.pi * t) * Real.sinh (b * x)) =
        (Real.exp (-b ^ 2 * t / 2) * (x / Real.sinh (b * x))) *
          (2 * Real.exp (-x ^ 2 / (2 * t)) /
            (Real.sqrt (2 * Real.pi * t) * x)) := by
    simpa [Cb, C0, K] using hC
  rw [hpos, (conditionedPositiveTransitionDensity_zero_eq_sinh_gaussian_factor ht hx hy), hExp, hCexplicit]
  dsimp [conditionedKernelShiftedZeroDensityRatio]
  field_simp [hy.ne', hsqrt, hsinhX, hsinhY, hsinhYD]

/-- The actual transition-density likelihood ratio from drift `b` with endpoint shift `b*t`,
compared to the unshifted zero-drift kernel, is antitone. This closes the zero-parameter endpoint
of the drift quantile comparison. -/
theorem conditionedPositiveTransitionDensity_shifted_zero_ratio_antitoneOn
    {b t x d : ℝ} (hb : 0 < b) (ht : 0 < t) (hx : 0 < x)
    (hd : 0 ≤ d) (hdt : d / t = b) :
    AntitoneOn
      (fun y => conditionedPositiveTransitionDensity b t x (y + d) /
        conditionedPositiveTransitionDensity 0 t x y) (Set.Ioi 0) := by
  have hR := conditionedKernelShiftedZeroDensityRatio_antitoneOn hb (div_pos hx ht) ht hd hdt
  have hC : 0 < Real.exp (-b ^ 2 * t / 2) * (x / Real.sinh (b * x)) := by
    positivity
  have hden (y : ℝ) (hy : 0 < y) :
      0 < conditionedPositiveTransitionDensity 0 t x y := by
    rw [conditionedPositiveTransitionDensity_zero_eq_sinh_gaussian_factor ht hx hy]
    positivity
  have hfactor (y : ℝ) (hy : 0 < y) :
      conditionedPositiveTransitionDensity b t x (y + d) /
        conditionedPositiveTransitionDensity 0 t x y =
      (Real.exp (-b ^ 2 * t / 2) * (x / Real.sinh (b * x))) *
        conditionedKernelShiftedZeroDensityRatio b (x / t) t d y := by
    rw [conditionedPositiveTransitionDensity_shifted_from_zero_eq_ratio hb ht hx hd hy]
    grind
  intro y₁ hy₁ y₂ hy₂ hy₁₂
  have hy₁' : 0 < y₁ := by assumption
  have hy₂' : 0 < y₂ := by assumption
  change conditionedPositiveTransitionDensity b t x _ /
      conditionedPositiveTransitionDensity 0 t x y₂ ≤
    conditionedPositiveTransitionDensity b t x _ /
      conditionedPositiveTransitionDensity 0 t x y₁
  rw [hfactor y₂ hy₂', hfactor y₁ hy₁']
  bound

/-- Under the probability-density normalizations, the shifted positive-drift kernel's CDF is at
least the unshifted BES(3) CDF. The hypothesis `m` is the shifted law's mass on the positive
half-line; the remaining mass lies to the left of the comparison's common support. -/
theorem conditionedPositiveTransitionDensity_shifted_zero_cdf_ge
    {b t x d m : ℝ} (hb : 0 < b) (ht : 0 < t) (hx : 0 < x)
    (hd : 0 ≤ d) (hdt : d / t = b)
    (hf : Integrable (fun y : ℝ => conditionedPositiveTransitionDensity 0 t x y)
      (volume : Measure ℝ))
    (hg : Integrable (fun y : ℝ => conditionedPositiveTransitionDensity b t x (y + d))
      (volume : Measure ℝ))
    (hng : ∀ y, 0 ≤ conditionedPositiveTransitionDensity b t x (y + d))
    (hunitf : ∫ y, conditionedPositiveTransitionDensity 0 t x y = 1)
    (hunitg : ∫ y, conditionedPositiveTransitionDensity b t x (y + d) = 1)
    (hmpos : 0 < m) (hmle : m ≤ 1)
    (hmass : (∫ y in Set.Ioi 0,
      conditionedPositiveTransitionDensity b t x (y + d) ∂(volume : Measure ℝ)) = m)
    (z : ℝ) :
    ∫ y in Set.Iic z, conditionedPositiveTransitionDensity 0 t x y ∂(volume : Measure ℝ) ≤
      ∫ y in Set.Iic z, conditionedPositiveTransitionDensity b t x (y + d)
        ∂(volume : Measure ℝ) := by
  let f : ℝ → ℝ := fun y => conditionedPositiveTransitionDensity 0 t x y
  let g : ℝ → ℝ := fun y => conditionedPositiveTransitionDensity b t x (y + d)
  let r : ℝ → ℝ := fun y => g y / f y
  have hzero : ∀ y, y ≤ 0 → f y = 0 := by
    intro y hy
    simp [f, conditionedPositiveTransitionDensity, hy]
  have hfpos : ∀ y, 0 < y → 0 < f y := by
    intro y hy
    change 0 < conditionedPositiveTransitionDensity 0 t x y
    rw [conditionedPositiveTransitionDensity_zero_eq_sinh_gaussian_factor ht hx hy]
    positivity
  have hgpos : ∀ y, 0 < y → 0 < g y := by
    intro y hy
    change 0 < conditionedPositiveTransitionDensity b t x (y + d)
    rw [conditionedPositiveTransitionDensity_eq_sinh_gaussian_factor hb ht hx
      (by linarith)]
    positivity
  have hratio : AntitoneOn r (Set.Ioi 0) := by
    have hR := conditionedPositiveTransitionDensity_shifted_zero_ratio_antitoneOn
      hb ht hx hd hdt
    intro y₁ hy₁ y₂ hy₂ hyy
    exact hR hy₁ hy₂ hyy
  have hrpos : ∀ y, 0 < y → 0 < r y := by
    intro y hy
    exact div_pos (hgpos y hy) (hfpos y hy)
  have hfactor : ∀ y, 0 < y → g y = r y * f y := by
    intro y hy
    dsimp [r]
    field_simp [ne_of_gt (hfpos y hy)]
  exact integral_Iic_ge_of_shiftedAntitoneDensityRatio
    (by assumption) (by assumption)
    (by assumption) hzero
    (by assumption) (by assumption)
    hmpos hmle (by assumption)
    (by assumption)
    (by assumption) (by assumption) z

end DOZZ.Proofs

end
