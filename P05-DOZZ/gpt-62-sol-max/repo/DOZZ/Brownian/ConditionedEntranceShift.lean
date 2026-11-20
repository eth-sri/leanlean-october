/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedEntranceProbability
public import DOZZ.Brownian.ConditionedKernelCDFOrder
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Drift shift bound for the conditioned entrance quantiles

The entrance density is a Gaussian factor times `y * sinh (ν*y) / ν`, with the Maxwell limit
`y^2` at zero drift. Comparing the shifted densities gives the upper common-quantile bound used
by the rational-drift coupling.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory Set Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The non-Gaussian factor in the entrance density, including its zero-drift limit. -/
noncomputable def conditionedEntranceShape (ν y : ℝ) : ℝ :=
  if ν = 0 then y ^ 2 else y * Real.sinh (ν * y) / ν

/-- The logarithmic derivative of the entrance shape in its positive state variable. -/
noncomputable def conditionedEntranceScore (ν y : ℝ) : ℝ :=
  if ν = 0 then 2 / y else 1 / y + conditionedKernelScore ν y

section
variable {ν y : ℝ} (hν : 0 ≤ ν) (hy : 0 < y)
include hν hy

private theorem conditionedEntranceShape_pos :
    0 < conditionedEntranceShape ν y := by
  by_cases hν0 : ν = 0
  · simp [conditionedEntranceShape, hν0, sq_pos_of_pos hy]
  · have hνpos  := lt_of_le_of_ne hν (Ne.symm hν0)
    simp only [conditionedEntranceShape, hν0, ite_false]
    exact div_pos (mul_pos hy (Real.sinh_pos_iff.mpr (mul_pos hνpos hy))) hνpos

private theorem hasDerivAt_conditionedEntranceShape :
    HasDerivAt (conditionedEntranceShape ν)
      (conditionedEntranceShape ν y * conditionedEntranceScore ν y) y := by
  by_cases hν0 : ν = 0
  · subst ν
    have hshape : conditionedEntranceShape (0 : ℝ) = fun z : ℝ => z ^ 2 := by
      funext z
      simp [conditionedEntranceShape]
    have hscore : conditionedEntranceScore (0 : ℝ) y = 2 / y := by
      simp [conditionedEntranceScore]
    rw [hshape, hscore]
    change HasDerivAt (fun z : ℝ => z ^ 2) (y ^ 2 * (2 / y)) y
    have h := (hasDerivAt_id y).pow 2
    convert h using 1
    · ext z
      rfl
    · simp only [id_eq]
      field_simp [hy.ne']
      ring_nf
  · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hν0)
    have harg : HasDerivAt (fun z : ℝ => ν * z) ν y := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul ν
    have hsinh := (Real.hasDerivAt_sinh (ν * y)).comp y harg
    have hprod := (hasDerivAt_id y).mul hsinh
    have hquot := hprod.div_const ν
    have hsinhpos  := Real.sinh_pos_iff.mpr (mul_pos hνpos hy)
    have halg : (Real.sinh (ν * y) + y * (Real.cosh (ν * y) * ν)) / ν =
        (y * Real.sinh (ν * y) / ν) *
          (1 / y + conditionedKernelScore ν y) := by
      dsimp [conditionedKernelScore]
      field_simp [hνpos.ne', hy.ne', hsinhpos.ne']
    have hshape : conditionedEntranceShape ν =
        (fun z : ℝ => z * Real.sinh (ν * z) / ν) := by
      funext z
      simp [conditionedEntranceShape, hν0]
    have hscore : conditionedEntranceScore ν y =
        1 / y + conditionedKernelScore ν y := by
      simp [conditionedEntranceScore, hν0]
    rw [hshape, hscore]
    have hquot' : HasDerivAt (fun z : ℝ => z * Real.sinh (ν * z) / ν)
        ((Real.sinh (ν * y) + y * (Real.cosh (ν * y) * ν)) / ν) y := by
      convert hquot using 1
      rfl
      norm_num
    exact hquot'.congr_deriv halg

end

private theorem conditionedEntranceScore_antitoneOn_state
    {ν : ℝ} (hν : 0 ≤ ν) : AntitoneOn (conditionedEntranceScore ν) (Set.Ioi 0) := by
  intro y hy z hz hyz
  by_cases hν0 : ν = 0
  · have hscore : conditionedEntranceScore ν = fun x : ℝ => 2 / x := by
      funext x
      simp [conditionedEntranceScore, hν0]
    rw [hscore]
    have hy' : 0 < y := by simpa using hy
    have hinv  := one_div_le_one_div_of_le hy'
        (by simpa using hyz)
    grind
  · have hνpos  := lt_of_le_of_ne hν (Ne.symm hν0)
    simp only [conditionedEntranceScore, hν0, ite_false]
    apply add_le_add
    · apply one_div_le_one_div_of_le <;> assumption
    · exact ((conditionedKernelScore_strictAntiOn_state hνpos).antitoneOn
        (by simpa using hy) (by simpa using hz) hyz)

private theorem conditionedEntranceScore_parameter_increment_upper
    {a b y : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hy : 0 < y) :
    conditionedEntranceScore b y - conditionedEntranceScore a y ≤ b - a := by
  have hb  := ha.trans hab
  by_cases ha0 : a = 0
  · subst a
    by_cases hb0 : b = 0
    · subst b
      simp [conditionedEntranceScore]
    · have hbpos  := lt_of_le_of_ne hb (Ne.symm hb0)
      simp only [conditionedEntranceScore, hb0, ite_false, ite_eq_left]
      have hs := conditionedKernelScore_zero_increment_bounds hbpos hy
      grind
  · have hapos  := lt_of_le_of_ne ha (Ne.symm ha0)
    by_cases hb0 : b = 0
    · have  := le_antisymm (by simpa [hb0] using hab) ha
      contradiction
    · 
      simp only [conditionedEntranceScore, ha0, hb0, ite_false]
      have hs := conditionedKernelScore_increment_bounds hapos hy hab
      linarith

private theorem conditionedEntranceScore_mixed_increment_upper
    {a b y z : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hy : 0 < y)
    (hyz : y ≤ z) :
    conditionedEntranceScore b z - conditionedEntranceScore a y ≤ b - a := by
  have hstate  :=
    conditionedEntranceScore_antitoneOn_state (le_trans ha hab)
      (Set.mem_Ioi.mpr hy) (Set.mem_Ioi.mpr (lt_of_lt_of_le hy hyz)) hyz
  have hparam := conditionedEntranceScore_parameter_increment_upper ha hab hy
  linarith

/-- The shifted entrance-density likelihood ratio. -/
noncomputable def conditionedEntranceShiftedDensityRatio
    (a b t d y : ℝ) : ℝ :=
  Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
    (conditionedEntranceShape b (y + d) / conditionedEntranceShape a y)

private theorem conditionedEntranceShiftedDensityRatio_hasDerivAt
    {a b t d y : ℝ} (ha : 0 ≤ a) (hb : a ≤ b) (ht : 0 < t)
    (hd : 0 ≤ d) (hy : 0 < y) :
    HasDerivAt (conditionedEntranceShiftedDensityRatio a b t d)
      (conditionedEntranceShiftedDensityRatio a b t d y *
        (-(d / t) + conditionedEntranceScore b (y + d) -
          conditionedEntranceScore a y)) y := by
  have hyD : 0 < y + d := by linarith
  have hlinear : HasDerivAt (fun z : ℝ => -(d / t) * z - d ^ 2 / (2 * t))
      (-(d / t)) y := by
    convert ((hasDerivAt_id y).const_mul (-(d / t))).sub_const (d ^ 2 / (2 * t)) using 1 <;> simp
  have hexp := (Real.hasDerivAt_exp _).comp y hlinear
  have hshapeB := hasDerivAt_conditionedEntranceShape (le_trans ha hb) hyD
  have hshift : HasDerivAt (fun z : ℝ => conditionedEntranceShape b (z + d))
      (conditionedEntranceShape b (y + d) * conditionedEntranceScore b (y + d)) y := by
    have harg : HasDerivAt (fun z : ℝ => z + d) 1 y := by
      simpa using (hasDerivAt_id y).add_const d
    convert hshapeB.comp y harg using 1
    · ext z
      rfl
    · ring
  have hshapeA := hasDerivAt_conditionedEntranceShape ha hy
  have hshapeApos := conditionedEntranceShape_pos ha hy
  have hquot := hshift.div hshapeA hshapeApos.ne'
  have hprod := hexp.mul hquot
  convert hprod using 1
  rfl
  · dsimp [conditionedEntranceShiftedDensityRatio]
    field_simp [hshapeApos.ne']
    ring_nf

/-- The shifted entrance likelihood ratio is antitone for the exact shift
`d = (b-a)t`, including the Maxwell endpoint `a=0`. -/
theorem conditionedEntranceShiftedDensityRatio_antitoneOn
    {a b t d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 < t)
    (hd : 0 ≤ d) (hshift : d / t = b - a) :
    AntitoneOn (conditionedEntranceShiftedDensityRatio a b t d) (Set.Ioi 0) := by
  have hcont : ContinuousOn (conditionedEntranceShiftedDensityRatio a b t d) (Set.Ioi 0) := by
    change ContinuousOn (fun y : ℝ => Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
      (conditionedEntranceShape b (y + d) / conditionedEntranceShape a y)) (Set.Ioi 0)
    have hshape : Continuous (conditionedEntranceShape b) := by
      unfold conditionedEntranceShape
      split_ifs <;> fun_prop
    have hshapeB : Continuous (fun y : ℝ => conditionedEntranceShape b (y + d)) :=
      hshape.comp (continuous_id.add continuous_const)
    have hshapeA : Continuous (conditionedEntranceShape a) := by
      unfold conditionedEntranceShape
      split_ifs <;> fun_prop
    have hratio : ContinuousOn
        (fun y : ℝ => conditionedEntranceShape b (y + d) / conditionedEntranceShape a y)
        (Set.Ioi 0) := by
      apply hshapeB.continuousOn.div hshapeA.continuousOn
      intro y hy
      exact (ne_of_gt (conditionedEntranceShape_pos ha (by simpa using hy)))
    have hexp : Continuous (fun y : ℝ => Real.exp (-(d / t) * y - d ^ 2 / (2 * t))) := by
      fun_prop
    exact hexp.continuousOn.mul hratio
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0) hcont
  · intro y hy
    exact (conditionedEntranceShiftedDensityRatio_hasDerivAt ha hab ht hd
      (by simpa using hy)).differentiableAt.differentiableWithinAt
  · intro y hy
    have hypos : 0 < y := by simpa using hy
    rw [(conditionedEntranceShiftedDensityRatio_hasDerivAt ha hab ht hd hypos).deriv]
    have hbracket : -(d / t) + conditionedEntranceScore b (y + d) -
        conditionedEntranceScore a y ≤ 0 := by
      rw [hshift]
      exact sub_nonpos.mpr (by
        have h := conditionedEntranceScore_mixed_increment_upper ha hab hypos
          (z := y + d) (by linarith [hd])
        linarith)
    exact mul_nonpos_of_nonneg_of_nonpos (by
      dsimp [conditionedEntranceShiftedDensityRatio]
      exact mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (div_pos
        (conditionedEntranceShape_pos (le_trans ha hab) (by linarith [hypos, hd]))
        (conditionedEntranceShape_pos ha hypos)))) hbracket

private theorem conditionedPositiveEntranceDensity_eq_shape
    {ν t y : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hy : 0 < y) :
    conditionedPositiveEntranceDensity ν t y =
      Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ)) *
        conditionedEntranceShape ν y *
          Real.exp (-(y ^ 2) / (2 * t) - ν ^ 2 * t / 2) := by
  by_cases hν0 : ν = 0
  · subst ν
    rw [conditionedPositiveEntranceDensity]
    simp only [le_rfl, ht, hy, and_self, ite_true]
    rw [Real.rpow_neg (le_of_lt ht)]
    have hpow  :=
      ne_of_gt (Real.rpow_pos_of_pos ht (3 / 2 : ℝ))
    have hshape : conditionedEntranceShape (0 : ℝ) y = y ^ 2 := by
      simp [conditionedEntranceShape]
    rw [hshape]
    field_simp [hpow]
    ring_nf
  · 
    have hshape : conditionedEntranceShape ν y = y * Real.sinh (ν * y) / ν := by
      simp [conditionedEntranceShape, hν0]
    rw [conditionedPositiveEntranceDensity, hshape]
    simp [hν, ht, hy, hν0]

private theorem conditionedPositiveEntranceDensity_shifted_factor
    {a b t d y : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 < t)
    (hd : 0 ≤ d) (hshift : d / t = b - a) (hy : 0 < y) :
    conditionedPositiveEntranceDensity b t (y + d) =
      Real.exp ((a ^ 2 - b ^ 2) * t / 2) *
        conditionedEntranceShiftedDensityRatio a b t d y *
          conditionedPositiveEntranceDensity a t y := by
  have hb  := ha.trans hab
  have hyD : 0 < y + d := by linarith
  rw [conditionedPositiveEntranceDensity_eq_shape hb ht hyD,
    conditionedPositiveEntranceDensity_eq_shape ha ht hy]
  dsimp [conditionedEntranceShiftedDensityRatio]
  have hshapeA  :=
    (conditionedEntranceShape_pos ha hy).ne'
  have hdrel : d = (b - a) * t := by
    have hmul := (div_eq_iff ht.ne').mp hshift
    nlinarith
  let A := (a ^ 2 - b ^ 2) * t / 2
  let B := -(d / t) * y - d ^ 2 / (2 * t)
  let C := -y ^ 2 / (2 * t) - a ^ 2 * t / 2
  have hExpFactor : Real.exp A * Real.exp B * Real.exp C =
      Real.exp (-((y + d) ^ 2) / (2 * t) - b ^ 2 * t / 2) := by
    calc
      Real.exp A * Real.exp B * Real.exp C = Real.exp (A + B) * Real.exp C := by
        rw [← Real.exp_add]
      _ = Real.exp (A + B + C) := by rw [← Real.exp_add]
      _ = Real.exp (-((y + d) ^ 2) / (2 * t) - b ^ 2 * t / 2) := by
        congr 1
        ring
  calc
    _ = Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ)) *
          conditionedEntranceShape b (y + d) * (Real.exp A * Real.exp B * Real.exp C) := by
            rw [← hExpFactor]
    _ = _ := by
      dsimp [A, B, C, conditionedEntranceShiftedDensityRatio]
      field_simp [hshapeA]

section
variable {ν t y : ℝ} (hν : 0 ≤ ν) (ht : 0 < t)
include hν ht

private theorem conditionedPositiveEntranceDensity_nonneg :
    0 ≤ conditionedPositiveEntranceDensity ν t y := by
  by_cases hy : 0 < y
  · by_cases hν0 : ν = 0
    · subst ν
      rw [conditionedPositiveEntranceDensity_zero_eq_heat ht hy]
      have hheat : 0 < brownianHeatDensity t y := by
        rw [brownianHeatDensity]
        simp only [ite_eq_left ht]
        positivity
      positivity
    · have hνpos  := lt_of_le_of_ne hν (Ne.symm hν0)
      rw [conditionedPositiveEntranceDensity_eq_zeroDriftTransition hνpos ht hy]
      exact conditionedPositiveTransitionDensity_nonneg (by norm_num) ht
        (mul_pos hνpos ht) y
  · 
    simp [conditionedPositiveEntranceDensity, hν, ht, hy]

private theorem conditionedPositiveEntranceDensity_zero_of_nonpos (hy : y ≤ 0) :
    conditionedPositiveEntranceDensity ν t y = 0 := by
  simp [conditionedPositiveEntranceDensity, hν, ht, hy]

end

/-- Translating the larger-drift entrance density left by its drift increment gives a CDF that
dominates the smaller-drift entrance CDF. -/
theorem conditionedPositiveEntranceDensity_shifted_cdf_ge
    {a b t d z : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 < t)
    (hd : 0 ≤ d) (hshift : d / t = b - a) :
    (∫ y in Set.Iic z, conditionedPositiveEntranceDensity a t y) ≤
      ∫ y in Set.Iic z, conditionedPositiveEntranceDensity b t (y + d) := by
  have hb := ha.trans hab
  refine integral_Iic_ge_of_shiftedAntitoneDensityRatio d z
    (integrable_conditionedPositiveEntranceDensity ha ht) (integrable_conditionedPositiveEntranceDensity hb ht)
    (fun _ => conditionedPositiveEntranceDensity_nonneg ha ht) (fun _ => conditionedPositiveEntranceDensity_nonneg hb ht)
    (fun _ => conditionedPositiveEntranceDensity_zero_of_nonpos ha ht)
    (conditionedPositiveEntranceDensity_integral_eq_one ha ht)
    (conditionedPositiveEntranceDensity_integral_eq_one hb ht)
    (fun _ hy => conditionedPositiveEntranceDensity_shifted_factor ha hab ht hd hshift hy) ?_
  intro y₁ hy₁ y₂ hy₂ hy₁₂
  exact mul_le_mul_of_nonneg_left
    (conditionedEntranceShiftedDensityRatio_antitoneOn ha hab ht hd hshift hy₁ hy₂ hy₁₂) (Real.exp_pos _).le

/-- The upper common-uniform drift bound for the conditioned entrance law. -/
theorem conditionedPositiveEntranceQuantile_drift_add
    {a b t u : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 < t)
    (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure b t)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure a t)) u + (b - a) * t := by
  have hb := ha.trans hab
  letI := isProbabilityMeasure_conditionedPositiveEntranceMeasure a t ha ht
  letI := isProbabilityMeasure_conditionedPositiveEntranceMeasure b t hb ht
  refine cdfGeneralizedQuantile_le_add hu hu1 (fun z => ?_)
  simpa only [conditionedPositiveEntranceMeasure_cdf_eq_integral ha ht,
    conditionedPositiveEntranceMeasure_cdf_eq_integral hb ht, integral_Iic_add_shift] using
    conditionedPositiveEntranceDensity_shifted_cdf_ge (z := z) ha hab ht
      (mul_nonneg (sub_nonneg.mpr hab) ht.le) (mul_div_cancel_right₀ (b - a) ht.ne')

end DOZZ.Proofs

end
