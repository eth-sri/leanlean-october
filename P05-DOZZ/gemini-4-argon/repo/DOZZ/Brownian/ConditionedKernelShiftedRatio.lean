/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelScoreParameter
public import DOZZ.Brownian.ConditionedKernelParameterRatio
public import DOZZ.Brownian.ConditionedKernelCDFOrder
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

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

private theorem shiftedRatio_heatDensity_sub_factor
    {t x y} (ht : 0 < t) :
    brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x) =
      Real.exp (-(x ^ 2 + y ^ 2) / (2 * t)) *
        (2 * Real.sinh (x * y / t) / Real.sqrt (2 * Real.pi * t)) := by
  simp only [brownianHeatDensity, ht, ite_true]
  rw [(show -((y - x) ^ 2) / (2 * t) = -(x ^ 2 + y ^ 2) / (2 * t) + x * y / t by field_simp [ht.ne']; ring), (show -((y + x) ^ 2) / (2 * t) = -(x ^ 2 + y ^ 2) / (2 * t) + -(x * y / t) by field_simp [ht.ne']; ring), Real.exp_add, Real.exp_add, Real.sinh_eq]
  field_simp [(show Real.sqrt (2 * Real.pi * t) ≠ 0 by positivity)]



/-- For strictly positive drift, the transition density's endpoint dependence is a fixed positive
factor times its Gaussian and two hyperbolic-sine factors. -/
theorem conditionedPositiveTransitionDensity_eq_sinh_gaussian_factor
    {ν t x y} (hν : 0 < ν) (ht : 0 < t) (hx : 0 < x) (hy : 0 < y) :
    conditionedPositiveTransitionDensity ν t x y =
      (2 * Real.exp (-ν ^ 2 * t / 2 - x ^ 2 / (2 * t)) /
        (Real.sqrt (2 * Real.pi * t) * Real.sinh (ν * x))) *
        (Real.exp (-y ^ 2 / (2 * t)) * Real.sinh (ν * y) * Real.sinh (x * y / t)) := by
  have shiftedRatio_conditionedH_sinh {ν} {x} (hν : 0 < ν) : conditionedH ν x = 2 * Real.exp (-ν * x) * Real.sinh (ν * x) := by
    have shiftedRatio_one_sub_exp_eq_sinh z : 1 - Real.exp (-2 * z) = 2 * Real.exp (-z) * Real.sinh z := by
      calc
        1 - Real.exp (-2 * z) =
            Real.exp ((-z) + z) - Real.exp ((-z) + (-z)) := by
              rw [show (-z) + z = 0 by ring, Real.exp_zero,
                show -2 * z = (-z) + (-z) by ring]
        _ = Real.exp (-z) * (Real.exp z - Real.exp (-z)) := by
              rw [Real.exp_add, Real.exp_add]
              ring
        _ = 2 * Real.exp (-z) * Real.sinh z := by
              rw [Real.sinh_eq]
              ring
    simp only [conditionedH, ite_eq_right (ne_of_gt hν)]
    simpa only [mul_assoc, neg_mul] using (shiftedRatio_one_sub_exp_eq_sinh (ν * x))
  simp [conditionedPositiveTransitionDensity, hν.le, ht, hx, hy,
    (shiftedRatio_heatDensity_sub_factor ht (x := x) (y := y)), (shiftedRatio_conditionedH_sinh (x := y) hν), (shiftedRatio_conditionedH_sinh (x := x) hν)]
  field_simp [(show 0 < Real.sqrt (2 * Real.pi * t) by positivity).ne', (Real.sinh_pos_iff.mpr (mul_pos hν hx)).ne']
  conv_lhs => rw [← Real.exp_add, ← Real.exp_add]
  conv_rhs => rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_injective
  field_simp [ht.ne']
  ring_nf


theorem hasDerivAt_sinhShift_ratio
    {a b y d} (ha : 0 < a) (hb : 0 < b) (hy : 0 < y) (hd : 0 ≤ d) :
    HasDerivAt (fun z : ℝ => Real.sinh (b * (z + d)) / Real.sinh (a * z))
      ((Real.sinh (b * (y + d)) / Real.sinh (a * y)) *
        (conditionedKernelScore b (y + d) - conditionedKernelScore a y)) y := by
  have hdenPos := Real.sinh_pos_iff.mpr (mul_pos ha hy)
  have hquot' : HasDerivAt
      (fun z => Real.sinh (b * (z + d)) / Real.sinh (a * z))
      ((Real.cosh (b * (y + d)) * b * Real.sinh (a * y) -
          Real.sinh (b * (y + d)) * (Real.cosh (a * y) * a)) /
        Real.sinh (a * y) ^ 2) y := by
    convert (((Real.hasDerivAt_sinh (b * (y + d))).comp y (show HasDerivAt (fun z => b * (z + d)) b y by convert ((hasDerivAt_id y).add_const d).const_mul b using 1 <;> simp)).div ((Real.hasDerivAt_sinh (a * y)).comp y (show HasDerivAt (fun z => a * z) a y by convert (hasDerivAt_id y).const_mul a using 1 <;> simp)) hdenPos.ne') using 1
    · funext z
      rfl
    · rfl
  convert hquot' using 1
  exact (show (Real.cosh (b * (y + d)) * b * Real.sinh (a * y) - Real.sinh (b * (y + d)) * (Real.cosh (a * y) * a)) / Real.sinh (a * y) ^ 2 = (Real.sinh (b * (y + d)) / Real.sinh (a * y)) * (conditionedKernelScore b (y + d) - conditionedKernelScore a y) by dsimp [conditionedKernelScore]; field_simp [(Real.sinh_pos_iff.mpr (mul_pos hb (by linarith))).ne', hdenPos.ne']).symm



/-- The likelihood ratio of the actual positive-drift transition densities under the shift
`d/t = b-a` is nonincreasing in the endpoint. This is the upper single-crossing input for
stochastic order. -/
theorem conditionedPositiveTransitionDensity_shifted_ratio_antitoneOn
    {a b t x d} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t)
    (hx : 0 < x) (hd : 0 ≤ d) (hshift : d / t = b - a) :
    AntitoneOn
      (fun y => conditionedPositiveTransitionDensity b t x (y + d) /
        conditionedPositiveTransitionDensity a t x y) (Set.Ioi 0) := by
  have hasDerivAt_conditionedKernelShiftedDensityRatio {b} {c} {t} {d} {y} (hb : 0 < b) (hc : 0 < c) (hy : 0 < y) (hd : 0 ≤ d) : HasDerivAt (conditionedKernelShiftedDensityRatio a b c t d) (conditionedKernelShiftedDensityRatio a b c t d y * (-(d / t) + (conditionedKernelScore b (y + d) - conditionedKernelScore a y) + (conditionedKernelScore c (y + d) - conditionedKernelScore c y))) y := by
    change HasDerivAt (fun z : ℝ =>
      Real.exp (-(d / t) * z - d ^ 2 / (2 * t)) *
        (Real.sinh (b * (z + d)) / Real.sinh (a * z)) *
          (Real.sinh (c * (z + d)) / Real.sinh (c * z))) _ y
    convert ((((Real.hasDerivAt_exp _).comp y (by convert ((hasDerivAt_id y).const_mul (-(d / t))).sub_const (d ^ 2 / (2 * t)) using 1 <;> simp)).mul (hasDerivAt_sinhShift_ratio ha hb hy hd)).mul (hasDerivAt_sinhShift_ratio hc hc hy hd)) using 1
    · rfl
    · dsimp [conditionedKernelShiftedDensityRatio]
      ring_nf
  have conditionedKernelShiftedDensityRatio_antitoneOn {c} {t} {d} (hc : 0 < c) (_ht : 0 < t) (hd : 0 ≤ d) (hshift : d / t = b - a) : AntitoneOn (conditionedKernelShiftedDensityRatio a b c t d) (Set.Ioi 0) := by
    have hb := lt_of_lt_of_le ha hab
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0) (by change ContinuousOn (fun y => Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) * (Real.sinh (b * (y + d)) / Real.sinh (a * y)) * (Real.sinh (c * (y + d)) / Real.sinh (c * y))) (Set.Ioi 0); exact ((show Continuous (fun y => Real.exp (-(d / t) * y - d ^ 2 / (2 * t))) by fun_prop).continuousOn.mul (by apply (show Continuous (fun y => Real.sinh (b * (y + d))) by fun_prop).continuousOn.div (show Continuous (fun y : ℝ => Real.sinh (a * y)) by fun_prop).continuousOn; intro y hy; exact (Real.sinh_pos_iff.mpr (mul_pos ha (by simpa using hy))).ne')).mul (by apply (show Continuous (fun y : ℝ => Real.sinh (c * (y + d))) by fun_prop).continuousOn.div (show Continuous (fun y : ℝ => Real.sinh (c * y)) by fun_prop).continuousOn; intro y hy; exact (Real.sinh_pos_iff.mpr (mul_pos hc (by simpa using hy))).ne'))
    · intro y hy
      exact (hasDerivAt_conditionedKernelShiftedDensityRatio hb hc (by simpa using hy) hd).differentiableAt.differentiableWithinAt
    · intro y hy
      have hypos : 0 < y := by simpa using hy
      rw [(hasDerivAt_conditionedKernelShiftedDensityRatio hb hc hypos hd).deriv]
      have := conditionedKernelScore_mixed_increment_upper ha hypos
        (z := y + d) (by linarith) hab
      have : conditionedKernelScore c (y + d) - conditionedKernelScore c y ≤ 0 := sub_nonpos.mpr (((conditionedKernelScore_strictAntiOn_state hc).antitoneOn) (Set.mem_Ioi.mpr hypos)
          (Set.mem_Ioi.mpr (by linarith)) (by linarith))
      exact mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ conditionedKernelShiftedDensityRatio a b c t d y by dsimp [conditionedKernelShiftedDensityRatio]; positivity) (by rw [hshift]; linarith)
  have conditionedPositiveTransitionDensity_shifted_eq_ratio {y} (hy : 0 < y) : conditionedPositiveTransitionDensity b t x (y + d) = (Real.exp (-((b ^ 2 - a ^ 2) * t / 2)) * (Real.sinh (a * x) / Real.sinh (b * x))) * conditionedKernelShiftedDensityRatio a b (x / t) t d y * conditionedPositiveTransitionDensity a t x y := by
    have hb := lt_of_lt_of_le ha hab
    have hyD : 0 < y + d := by linarith
    have hca := (Real.sinh_pos_iff.mpr (mul_pos ha hx)).ne'
    have hcb := (Real.sinh_pos_iff.mpr (mul_pos hb hx)).ne'
    have hcoef :
        2 * Real.exp (-b ^ 2 * t / 2 - x ^ 2 / (2 * t)) /
            (Real.sqrt (2 * Real.pi * t) * Real.sinh (b * x)) =
        Real.exp (-((b ^ 2 - a ^ 2) * t / 2)) *
          (Real.sinh (a * x) / Real.sinh (b * x)) *
            (2 * Real.exp (-a ^ 2 * t / 2 - x ^ 2 / (2 * t)) /
              (Real.sqrt (2 * Real.pi * t) * Real.sinh (a * x))) := by
      field_simp [hca, hcb]
      rw [← Real.exp_add]
      congr 1
      field_simp [ht.ne']
      ring_nf
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
    field_simp [hca, hcb, ((Real.sinh_pos_iff.mpr (mul_pos (div_pos hx ht) hy)).ne'), ((Real.sinh_pos_iff.mpr (mul_pos hb hyD)).ne'), ((Real.sinh_pos_iff.mpr (mul_pos ha hy)).ne')]
  let C := Real.exp (-((b ^ 2 - a ^ 2) * t / 2)) *
    (Real.sinh (a * x) / Real.sinh (b * x))
  have hdenPos y (hy : 0 < y) :
      0 < conditionedPositiveTransitionDensity a t x y := by
    rw [conditionedPositiveTransitionDensity_eq_sinh_gaussian_factor ha ht hx hy]
    positivity
  have hfactor y (hy : 0 < y) :
      conditionedPositiveTransitionDensity b t x (y + d) /
        conditionedPositiveTransitionDensity a t x y =
      C * conditionedKernelShiftedDensityRatio a b (x / t) t d y := by
    rw [conditionedPositiveTransitionDensity_shifted_eq_ratio hy]
    dsimp [C]
    field_simp [(hdenPos y hy).ne']
  intro y₁ hy₁ y₂ hy₂ hy₁₂
  change conditionedPositiveTransitionDensity b t x (y₂ + d) /
      conditionedPositiveTransitionDensity a t x y₂ ≤
    conditionedPositiveTransitionDensity b t x (y₁ + d) /
      conditionedPositiveTransitionDensity a t x y₁
  rw [hfactor y₂ (show 0 < y₂ by simpa using hy₂), hfactor y₁ (show 0 < y₁ by simpa using hy₁)]
  exact mul_le_mul_of_nonneg_left ((conditionedKernelShiftedDensityRatio_antitoneOn (div_pos hx ht) ht hd hshift) hy₁ hy₂ hy₁₂) (le_of_lt (by dsimp [C]; exact mul_pos (Real.exp_pos _) (div_pos (Real.sinh_pos_iff.mpr (mul_pos ha hx)) (Real.sinh_pos_iff.mpr (mul_pos (lt_of_lt_of_le ha hab) hx)))))

/-- Endpoint-dependent likelihood ratio for shifting a positive-drift transition density against
the zero-drift BES(3) kernel. The factor `sinh (b (y+d)) / y` is the continuous zero-parameter
limit of the first hyperbolic quotient in `conditionedKernelShiftedDensityRatio`. -/
noncomputable def conditionedKernelShiftedZeroDensityRatio
    (b c t d y : ℝ) : ℝ :=
  Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
    (Real.sinh (b * (y + d)) / y) *
      (Real.sinh (c * (y + d)) / Real.sinh (c * y))





theorem conditionedPositiveTransitionDensity_zero_eq_sinh_gaussian_factor
    {t x y} (ht : 0 < t) (hx : 0 < x) (hy : 0 < y) :
    conditionedPositiveTransitionDensity 0 t x y =
      (2 * Real.exp (-x ^ 2 / (2 * t)) /
        (Real.sqrt (2 * Real.pi * t) * x)) *
        (Real.exp (-y ^ 2 / (2 * t)) * y * Real.sinh (x / t * y)) := by
  simp [conditionedPositiveTransitionDensity, conditionedH, ht, hx, hy]
  rw [(shiftedRatio_heatDensity_sub_factor ht (x := x) (y := y))]
  have hexp : Real.exp (-(x ^ 2 + y ^ 2) / (2 * t)) =
      Real.exp (-x ^ 2 / (2 * t)) * Real.exp (-y ^ 2 / (2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp [ht.ne']
    ring_nf
  rw [hexp, (show x * y / t = x / t * y by ring)]
  field_simp [hx.ne', (show Real.sqrt (2 * Real.pi * t) ≠ 0 by positivity)]



/-- Under the probability-density normalizations, the shifted positive-drift kernel's CDF is at
least the unshifted BES(3) CDF. The hypothesis `m` is the shifted law's mass on the positive
half-line; the remaining mass lies to the left of the comparison's common support. -/
theorem conditionedPositiveTransitionDensity_shifted_zero_cdf_ge
    {b t x d m} (hb : 0 < b) (ht : 0 < t) (hx : 0 < x)
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
    z :
    ∫ y in Set.Iic z, conditionedPositiveTransitionDensity 0 t x y ∂(volume : Measure ℝ) ≤
      ∫ y in Set.Iic z, conditionedPositiveTransitionDensity b t x (y + d)
        ∂(volume : Measure ℝ) := by
  have hasDerivAt_conditionedKernelShiftedZeroDensityRatio {c} {t} {d} {y} (hc : 0 < c) (ht : 0 < t) (hd : 0 ≤ d) (hy : 0 < y) : HasDerivAt (conditionedKernelShiftedZeroDensityRatio b c t d) (conditionedKernelShiftedZeroDensityRatio b c t d y * (-(d / t) + (conditionedKernelScore b (y + d) - 1 / y) + (conditionedKernelScore c (y + d) - conditionedKernelScore c y))) y := by
    have hasDerivAt_shiftedExpFactor {t} {d} {y} (_ht : 0 < t) : HasDerivAt (fun z => Real.exp (-(d / t) * z - d ^ 2 / (2 * t))) (Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) * (-(d / t))) y := by
      have harg : HasDerivAt (fun z => -(d / t) * z - d ^ 2 / (2 * t))
          (-(d / t)) y := by
        convert ((hasDerivAt_id y).const_mul (-(d / t))).add_const (-(d ^ 2 / (2 * t))) using 1
        · ext z
          simp [sub_eq_add_neg]
        · ring
      exact (Real.hasDerivAt_exp _).comp y harg
    have hasDerivAt_sinhShift_div_state : HasDerivAt (fun z => Real.sinh (b * (z + d)) / z) ((Real.sinh (b * (y + d)) / y) * (conditionedKernelScore b (y + d) - 1 / y)) y := by
      have hquot' : HasDerivAt (fun z => Real.sinh (b * (z + d)) / z)
          ((Real.cosh (b * (y + d)) * b * y - Real.sinh (b * (y + d))) / y ^ 2) y := by
        convert (((Real.hasDerivAt_sinh (b * (y + d))).comp y (by convert ((hasDerivAt_id y).add_const d).const_mul b using 1 <;> simp)).div (hasDerivAt_id y) hy.ne') using 1
        · ext z
          simp [mul_add]
        · simp [mul_add, id_eq]
      convert hquot' using 1
      exact (show (Real.cosh (b * (y + d)) * b * y - Real.sinh (b * (y + d))) / y ^ 2 = (Real.sinh (b * (y + d)) / y) * (conditionedKernelScore b (y + d) - 1 / y) by dsimp [conditionedKernelScore]; field_simp [hy.ne', ((Real.sinh_pos_iff.mpr (mul_pos hb (by linarith))).ne' : Real.sinh (b * (y + d)) ≠ 0)]).symm
    change HasDerivAt (fun z : ℝ =>
      (Real.exp (-(d / t) * z - d ^ 2 / (2 * t)) *
        (Real.sinh (b * (z + d)) / z)) *
          (Real.sinh (c * (z + d)) / Real.sinh (c * z))) _ y
    convert (((hasDerivAt_shiftedExpFactor ht (d := d) (y := y)).mul (hasDerivAt_sinhShift_div_state)).mul (hasDerivAt_sinhShift_ratio hc hc hy hd)) using 1
    · dsimp [conditionedKernelShiftedZeroDensityRatio]
      ring_nf
  have conditionedPositiveTransitionDensity_shifted_zero_ratio_antitoneOn : AntitoneOn (fun y => conditionedPositiveTransitionDensity b t x (y + d) / conditionedPositiveTransitionDensity 0 t x y) (Set.Ioi 0) := by
    have conditionedPositiveTransitionDensity_shifted_from_zero_eq_ratio {y} (hy : 0 < y) : conditionedPositiveTransitionDensity b t x (y + d) = (Real.exp (-b ^ 2 * t / 2) * (x / Real.sinh (b * x))) * conditionedKernelShiftedZeroDensityRatio b (x / t) t d y * conditionedPositiveTransitionDensity 0 t x y := by
      have hc := div_pos hx ht
      have hyD : 0 < y + d := by linarith
      have hsqrt : Real.sqrt (2 * Real.pi * t) ≠ 0 := by positivity
      have hsinhX := (Real.sinh_pos_iff.mpr (mul_pos hb hx)).ne'
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
      rw [(conditionedPositiveTransitionDensity_eq_sinh_gaussian_factor hb ht hx hyD), (conditionedPositiveTransitionDensity_zero_eq_sinh_gaussian_factor ht hx hy), hExp, (show 2 * Real.exp (-b ^ 2 * t / 2 - x ^ 2 / (2 * t)) / (Real.sqrt (2 * Real.pi * t) * Real.sinh (b * x)) = (Real.exp (-b ^ 2 * t / 2) * (x / Real.sinh (b * x))) * (2 * Real.exp (-x ^ 2 / (2 * t)) / (Real.sqrt (2 * Real.pi * t) * x)) by simpa [Cb, C0, K] using hC)]
      dsimp [conditionedKernelShiftedZeroDensityRatio]
      field_simp [hy.ne', hsqrt, hsinhX, ((Real.sinh_pos_iff.mpr (mul_pos hc hy)).ne'), ((Real.sinh_pos_iff.mpr (mul_pos hc hyD)).ne')]
    have conditionedKernelShiftedZeroDensityRatio_antitoneOn {c} {t} {d} (hc : 0 < c) (ht : 0 < t) (hd : 0 ≤ d) (hdt : d / t = b) : AntitoneOn (conditionedKernelShiftedZeroDensityRatio b c t d) (Set.Ioi 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) (by change ContinuousOn (fun y => Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) * (Real.sinh (b * (y + d)) / y) * (Real.sinh (c * (y + d)) / Real.sinh (c * y))) (Set.Ioi 0); exact ((show Continuous (fun y => Real.exp (-(d / t) * y - d ^ 2 / (2 * t))) by fun_prop).continuousOn.mul (by apply (Real.continuous_sinh.comp (continuous_const.mul (continuous_id.add continuous_const))).continuousOn.div continuousOn_id; intro y hy; exact ne_of_gt (by simpa using hy))).mul (by apply (Real.continuous_sinh.comp (continuous_const.mul (continuous_id.add continuous_const))).continuousOn.div (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).continuousOn; intro y hy; exact (Real.sinh_pos_iff.mpr (mul_pos hc (by simpa using hy))).ne')) ?_ ?_
      · intro y hy
        exact (hasDerivAt_conditionedKernelShiftedZeroDensityRatio hc ht hd (by simpa using hy)).differentiableAt.differentiableWithinAt
      · intro y hy
        have hy' : 0 < y := by simpa using hy
        rw [(hasDerivAt_conditionedKernelShiftedZeroDensityRatio hc ht hd hy').deriv]
        have hyD : 0 < y + d := by linarith
        have : conditionedKernelScore b (y + d) ≤ conditionedKernelScore b y := ((conditionedKernelScore_strictAntiOn_state hb).antitoneOn) (Set.mem_Ioi.mpr hy') (Set.mem_Ioi.mpr hyD) (by linarith)
        have := conditionedKernelScore_zero_increment_bounds hb hy'
        have : conditionedKernelScore c (y + d) ≤ conditionedKernelScore c y := ((conditionedKernelScore_strictAntiOn_state hc).antitoneOn) (Set.mem_Ioi.mpr hy') (Set.mem_Ioi.mpr hyD) (by linarith)
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (by dsimp [conditionedKernelShiftedZeroDensityRatio]; positivity)) (by rw [hdt]; linarith)
    have hden y (hy : 0 < y) :
        0 < conditionedPositiveTransitionDensity 0 t x y := by
      rw [conditionedPositiveTransitionDensity_zero_eq_sinh_gaussian_factor ht hx hy]
      positivity
    have hfactor y (hy : 0 < y) :
        conditionedPositiveTransitionDensity b t x (y + d) /
          conditionedPositiveTransitionDensity 0 t x y =
        (Real.exp (-b ^ 2 * t / 2) * (x / Real.sinh (b * x))) *
          conditionedKernelShiftedZeroDensityRatio b (x / t) t d y := by
      rw [conditionedPositiveTransitionDensity_shifted_from_zero_eq_ratio hy]
      field_simp [(hden y hy).ne']
    intro y₁ hy₁ y₂ hy₂ hy₁₂
    change conditionedPositiveTransitionDensity b t x (y₂ + d) /
        conditionedPositiveTransitionDensity 0 t x y₂ ≤
      conditionedPositiveTransitionDensity b t x (y₁ + d) /
        conditionedPositiveTransitionDensity 0 t x y₁
    rw [hfactor y₂ (show 0 < y₂ by simpa using hy₂), hfactor y₁ (show 0 < y₁ by simpa using hy₁)]
    exact mul_le_mul_of_nonneg_left ((conditionedKernelShiftedZeroDensityRatio_antitoneOn (div_pos hx ht) ht hd hdt) hy₁ hy₂ hy₁₂) (le_of_lt (by positivity))
  let f : ℝ → ℝ := fun y => conditionedPositiveTransitionDensity 0 t x y
  let g : ℝ → ℝ := fun y => conditionedPositiveTransitionDensity b t x (y + d)
  let r : ℝ → ℝ := fun y => g y / f y
  have hfpos : ∀ y, 0 < y → 0 < f y := by
    intro y hy
    change 0 < conditionedPositiveTransitionDensity 0 t x y
    rw [conditionedPositiveTransitionDensity_zero_eq_sinh_gaussian_factor ht hx hy]
    positivity
  have hgpos : ∀ y, 0 < y → 0 < g y := by
    intro y hy
    change 0 < conditionedPositiveTransitionDensity b t x (y + d)
    rw [conditionedPositiveTransitionDensity_eq_sinh_gaussian_factor hb ht hx
      (by linarith [hd])]
    positivity
  have hfactor : ∀ y, 0 < y → g y = r y * f y := by
    intro y hy
    dsimp [r]
    field_simp [ne_of_gt (hfpos y hy)]
  exact integral_Iic_ge_of_shiftedAntitoneDensityRatio
    (by simpa [f] using hf) (by simpa [g] using hg)
    (by simpa [g] using hng) (show ∀ y, y ≤ 0 → f y = 0 by intro y hy; simp [f, conditionedPositiveTransitionDensity, hy])
    (by simpa [f] using hunitf) (by simpa [g] using hunitg)
    hmpos hmle (by simpa [g] using hmass)
    (by simpa [f, g] using hfactor)
    (by simpa [r] using (show ∀ y, 0 < y → 0 < r y by intro y hy; exact div_pos (hgpos y hy) (hfpos y hy))) (by simpa [r] using (show AntitoneOn r (Set.Ioi 0) by intro y₁ hy₁ y₂ hy₂ hyy; exact (conditionedPositiveTransitionDensity_shifted_zero_ratio_antitoneOn) hy₁ hy₂ hyy)) z

end DOZZ.Proofs

end
