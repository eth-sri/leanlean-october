/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelScoreParameter
public import DOZZ.Statements.Brownian.ConditionedPositiveTransitionDensity
public import DOZZ.Statements.Brownian.ConditionedPositiveEntranceDensity
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Monotone likelihood ratio in the drift parameter

The ordered coupling compares conditioned transition densities by their likelihood ratios. The
hyperbolic factor `sinh (b*y) / sinh (a*y)` is nondecreasing in the state when `0 < a ≤ b`.
-/

@[expose] public section

open Filter Topology

namespace DOZZ.Proofs

private theorem conditionedH_pos_of_pos {ν x} (hν : 0 < ν) (hx : 0 < x) :
    0 < conditionedH ν x := by
  simp only [conditionedH, hν.ne']
  apply sub_pos.mpr
  apply (Real.exp_lt_one_iff).2
  nlinarith

private theorem brownianHeatDensity_sub_pos
    {t x y} (ht : 0 < t) (hx : 0 < x) (hy : 0 < y) :
    0 < brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x) := by
  simpa [brownianHeatDensity, ht] using ((div_lt_div_iff_of_pos_right (by positivity)).2 (Real.exp_lt_exp.mpr (by apply div_lt_div_of_pos_right _ (mul_pos (by norm_num) ht); nlinarith)))

private theorem one_sub_exp_neg_two_mul_eq_two_exp_neg_mul_sinh z :
    1 - Real.exp (-2 * z) = 2 * Real.exp (-z) * Real.sinh z := by
  calc
    1 - Real.exp (-2 * z) =
        Real.exp ((-z) + z) - Real.exp ((-z) + (-z)) := by
          rw [show (1 : ℝ) = Real.exp ((-z) + z) by
            rw [show (-z) + z = 0 by ring, Real.exp_zero],
            show Real.exp (-2 * z) = Real.exp ((-z) + (-z)) by congr 1; ring]
    _ = Real.exp (-z) * (Real.exp z - Real.exp (-z)) := by
          rw [Real.exp_add, Real.exp_add]
          ring
    _ = 2 * Real.exp (-z) * Real.sinh z := by
          rw [Real.sinh_eq]
          ring

/-- The hyperbolic likelihood ratio for two positive drift parameters. -/
noncomputable def conditionedKernelParameterRatio (a b y : ℝ) : ℝ :=
  Real.sinh (b * y) / Real.sinh (a * y)


/-- Increasing the drift parameter makes the hyperbolic likelihood ratio nondecreasing in the
state. -/
theorem conditionedKernelParameterRatio_monotoneOn_state
    {a b} (ha : 0 < a) (hab : a ≤ b) :
    MonotoneOn (conditionedKernelParameterRatio a b) (Set.Ioi 0) := by
  have hasDerivAt_conditionedKernelParameterRatio {b} {y} (hb : 0 < b) (hy : 0 < y) : HasDerivAt (conditionedKernelParameterRatio a b) (conditionedKernelParameterRatio a b y * (conditionedKernelScore b y - conditionedKernelScore a y)) y := by
    have hApos := Real.sinh_pos_iff.mpr (mul_pos ha hy)
    have hquot' : HasDerivAt (fun z => Real.sinh (b * z) / Real.sinh (a * z))
        ((Real.cosh (b * y) * b * Real.sinh (a * y) -
            Real.sinh (b * y) * (Real.cosh (a * y) * a)) /
          Real.sinh (a * y) ^ 2) y := by
      convert (((Real.hasDerivAt_sinh (b * y)).comp y (by simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul b)).div ((Real.hasDerivAt_sinh (a * y)).comp y (by simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul a)) hApos.ne') using 1
      · funext z
        rfl
      · rfl
    change HasDerivAt (fun z : ℝ =>
        Real.sinh (b * z) / Real.sinh (a * z))
      (conditionedKernelParameterRatio a b y *
        (conditionedKernelScore b y - conditionedKernelScore a y)) y
    convert hquot' using 1
    exact (show (Real.cosh (b * y) * b * Real.sinh (a * y) - Real.sinh (b * y) * (Real.cosh (a * y) * a)) / Real.sinh (a * y) ^ 2 = conditionedKernelParameterRatio a b y * (conditionedKernelScore b y - conditionedKernelScore a y) by dsimp [conditionedKernelParameterRatio, conditionedKernelScore]; field_simp [hApos.ne', (Real.sinh_pos_iff.mpr (mul_pos hb hy)).ne']).symm
  have hb := lt_of_lt_of_le ha hab
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) (by change ContinuousOn (fun y => Real.sinh (b * y) / Real.sinh (a * y)) (Set.Ioi 0); apply (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).continuousOn.div (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).continuousOn; intro y hy; exact (Real.sinh_pos_iff.mpr (mul_pos ha (by simpa using hy))).ne') ?_ ?_
  · intro y hy
    exact (hasDerivAt_conditionedKernelParameterRatio hb (by simpa using hy)).differentiableAt.differentiableWithinAt
  · intro y hy
    have hy' : 0 < y := by simpa using hy
    rw [(hasDerivAt_conditionedKernelParameterRatio hb hy').deriv]
    exact mul_nonneg (le_of_lt (by simp only [conditionedKernelParameterRatio]; exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hb hy')) (Real.sinh_pos_iff.mpr (mul_pos ha hy')))) (conditionedKernelScore_increment_bounds ha hy' hab).1




/-- The likelihood ratio of positive-drift entrance densities is nondecreasing in the terminal
state. This is the initial-time counterpart of the transition-kernel MLR comparison. -/
theorem conditionedPositiveEntranceDensity_ratio_monotoneOn_state
    {a b t} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) :
    MonotoneOn
      (fun y => conditionedPositiveEntranceDensity b t y /
        conditionedPositiveEntranceDensity a t y) (Set.Ioi 0) := by
  have conditionedPositiveEntranceDensity_pos_of_pos {ν} {t} {y} (hν : 0 < ν) (ht : 0 < t) (hy : 0 < y) : 0 < conditionedPositiveEntranceDensity ν t y := by
    simp only [conditionedPositiveEntranceDensity, hν.le, ht, hy, and_self, ite_true, hν.ne']
    positivity
  have conditionedPositiveEntranceDensity_eq_parameter_ratio_mul {y} (hy : 0 < y) : conditionedPositiveEntranceDensity b t y = (a / b * Real.exp (-((b ^ 2 - a ^ 2) * t / 2))) * conditionedKernelParameterRatio a b y * conditionedPositiveEntranceDensity a t y := by
    have hb := lt_of_lt_of_le ha hab
    simp [conditionedPositiveEntranceDensity, ha.le, hb.le, ht, hy, ha.ne', hb.ne',
      conditionedKernelParameterRatio]
    field_simp [ha.ne', hb.ne']
    rw [← Real.exp_add]
    congr 1
    field_simp [ht.ne']
    ring
  have := lt_of_lt_of_le ha hab
  have hfactor y (hy : 0 < y) :
      conditionedPositiveEntranceDensity b t y /
        conditionedPositiveEntranceDensity a t y =
          (a / b * Real.exp (-((b ^ 2 - a ^ 2) * t / 2))) *
            conditionedKernelParameterRatio a b y := by
    rw [conditionedPositiveEntranceDensity_eq_parameter_ratio_mul hy]
    field_simp [(conditionedPositiveEntranceDensity_pos_of_pos ha ht hy).ne']
  intro x hx y hy hxy
  have hx' : 0 < x := by simpa using hx
  have hy' : 0 < y := by simpa using hy
  change conditionedPositiveEntranceDensity b t x /
      conditionedPositiveEntranceDensity a t x ≤
    conditionedPositiveEntranceDensity b t y /
      conditionedPositiveEntranceDensity a t y
  rw [hfactor x hx', hfactor y hy']
  exact mul_le_mul_of_nonneg_left ((conditionedKernelParameterRatio_monotoneOn_state ha hab) hx' hy' hxy) (le_of_lt (by positivity))


/-- For fixed positive time and starting state, the ratio of transition densities with positive
drifts `a≤b` is nondecreasing in the endpoint. -/
theorem conditionedPositiveTransitionDensity_ratio_monotoneOn_state
    {a b t x} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) (hx : 0 < x) :
    MonotoneOn
      (fun y => conditionedPositiveTransitionDensity b t x y /
        conditionedPositiveTransitionDensity a t x y) (Set.Ioi 0) := by
  have conditionedPositiveTransitionDensity_pos_of_pos {ν} {t} {x} {y} (hν : 0 < ν) (ht : 0 < t) (hx : 0 < x) (hy : 0 < y) : 0 < conditionedPositiveTransitionDensity ν t x y := by
    simp only [conditionedPositiveTransitionDensity, hν.le, ht, hx, hy, and_self, ite_true]
    exact div_pos
      (mul_pos (mul_pos (Real.exp_pos _) (brownianHeatDensity_sub_pos ht hx hy))
        (conditionedH_pos_of_pos hν hy))
      (conditionedH_pos_of_pos hν hx)
  have conditionedPositiveTransitionDensity_eq_parameter_ratio_mul {y} (hy : 0 < y) : conditionedPositiveTransitionDensity b t x y = (Real.exp (-((b ^ 2 - a ^ 2) * t / 2) - (b - a) * x) * conditionedH a x / conditionedH b x) * conditionedKernelParameterRatio a b y * conditionedPositiveTransitionDensity a t x y := by
    have hb := lt_of_lt_of_le ha hab
    have hHay : conditionedH a y = 2 * Real.exp (-a * y) * Real.sinh (a * y) := by
      simp only [conditionedH, ite_eq_right (ne_of_gt ha)]
      simpa only [mul_assoc, neg_mul] using
        one_sub_exp_neg_two_mul_eq_two_exp_neg_mul_sinh (a * y)
    have hHby : conditionedH b y = 2 * Real.exp (-b * y) * Real.sinh (b * y) := by
      simp only [conditionedH, ite_eq_right (ne_of_gt hb)]
      simpa only [mul_assoc, neg_mul] using
        one_sub_exp_neg_two_mul_eq_two_exp_neg_mul_sinh (b * y)
    have hHax : conditionedH a x = 2 * Real.exp (-a * x) * Real.sinh (a * x) := by
      simp only [conditionedH, ite_eq_right (ne_of_gt ha)]
      simpa only [mul_assoc, neg_mul] using
        one_sub_exp_neg_two_mul_eq_two_exp_neg_mul_sinh (a * x)
    have hHbx : conditionedH b x = 2 * Real.exp (-b * x) * Real.sinh (b * x) := by
      simp only [conditionedH, ite_eq_right (ne_of_gt hb)]
      simpa only [mul_assoc, neg_mul] using
        one_sub_exp_neg_two_mul_eq_two_exp_neg_mul_sinh (b * x)
    simp [conditionedPositiveTransitionDensity, ha.le, hb.le, ht, hx, hy,
      hHay, hHby, hHax, hHbx, conditionedKernelParameterRatio]
    field_simp [(conditionedH_pos_of_pos ha hx).ne', (conditionedH_pos_of_pos hb hx).ne', (Real.sinh_pos_iff.mpr (mul_pos ha hy)).ne', (Real.sinh_pos_iff.mpr (mul_pos hb hy)).ne', (brownianHeatDensity_sub_pos ht hx hy).ne']
    conv_rhs => rw [← Real.exp_add, ← Real.exp_add]
    conv_lhs => rw [← Real.exp_add]
    congr 1
    ring_nf
  have hfactor y (hy : 0 < y) :
      conditionedPositiveTransitionDensity b t x y /
        conditionedPositiveTransitionDensity a t x y =
          (Real.exp (-((b ^ 2 - a ^ 2) * t / 2) - (b - a) * x) *
            conditionedH a x / conditionedH b x) *
            conditionedKernelParameterRatio a b y := by
    rw [conditionedPositiveTransitionDensity_eq_parameter_ratio_mul hy]
    field_simp [(conditionedPositiveTransitionDensity_pos_of_pos ha ht hx hy).ne']
  intro y₁ hy₁ y₂ hy₂ hy₁₂
  have hy₁' : 0 < y₁ := by simpa using hy₁
  have hy₂' : 0 < y₂ := by simpa using hy₂
  change conditionedPositiveTransitionDensity b t x y₁ /
      conditionedPositiveTransitionDensity a t x y₁ ≤
    conditionedPositiveTransitionDensity b t x y₂ /
      conditionedPositiveTransitionDensity a t x y₂
  rw [hfactor y₁ hy₁', hfactor y₂ hy₂']
  exact mul_le_mul_of_nonneg_left ((conditionedKernelParameterRatio_monotoneOn_state ha hab) hy₁' hy₂' hy₁₂) (le_of_lt (div_pos (mul_pos (Real.exp_pos _) (conditionedH_pos_of_pos ha hx)) (conditionedH_pos_of_pos (lt_of_lt_of_le ha hab) hx)))

/-- The likelihood-ratio factor that appears when comparing a positive drift with zero drift. -/
noncomputable def conditionedKernelZeroParameterRatio (b y : ℝ) : ℝ :=
  Real.sinh (b * y) / (b * y)

private theorem conditionedKernelScore_ge_reciprocal
    {b y} (hb : 0 < b) (hy : 0 < y) :
    1 / y ≤ conditionedKernelScore b y := by
  have hbound : ∀ᶠ a : ℝ in 𝓝[Set.Ioi 0] (0 : ℝ),
      conditionedKernelScore a y ≤ conditionedKernelScore b y := by
    filter_upwards [(by exact Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hb)), self_mem_nhdsWithin] with a hab ha
    linarith [(conditionedKernelScore_increment_bounds (by simpa using ha) hy hab.le).1]
  exact le_of_tendsto ((conditionedKernelScore_tendsto_zero_parameter hy).mono_left (nhdsWithin_mono 0 (by intro a ha; exact ne_of_gt ha))) hbound

/-- At the zero-parameter endpoint, the score increment from its limiting value `1/y` is
nonnegative and at most the parameter itself. -/
theorem conditionedKernelScore_zero_increment_bounds
    {b y} (hb : 0 < b) (hy : 0 < y) :
    0 ≤ conditionedKernelScore b y - 1 / y ∧
      conditionedKernelScore b y - 1 / y ≤ b := by
  have := conditionedKernelScore_ge_reciprocal hb hy
  have hbound : ∀ᶠ a : ℝ in 𝓝[Set.Ioi 0] (0 : ℝ),
      conditionedKernelScore b y - conditionedKernelScore a y ≤ b := by
    filter_upwards [(by exact Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hb)), self_mem_nhdsWithin] with a hab ha
    have : 0 ≤ a := le_of_lt (by simpa using ha)
    linarith [(conditionedKernelScore_increment_bounds (by simpa using ha) hy hab.le).2]
  exact ⟨by linarith,
    le_of_tendsto (tendsto_const_nhds.sub ((conditionedKernelScore_tendsto_zero_parameter hy).mono_left (nhdsWithin_mono 0 (by intro a ha; exact ne_of_gt ha)))) hbound⟩


/-- The zero-parameter likelihood ratio is nondecreasing in the endpoint. Its logarithmic
derivative is the positive-parameter score minus its zero-drift limit `1/y`. -/
theorem conditionedKernelZeroParameterRatio_monotoneOn_state
    {b} (hb : 0 < b) :
    MonotoneOn (conditionedKernelZeroParameterRatio b) (Set.Ioi 0) := by
  have hasDerivAt_conditionedKernelZeroParameterRatio {y} (hy : 0 < y) : HasDerivAt (conditionedKernelZeroParameterRatio b) (conditionedKernelZeroParameterRatio b y * (conditionedKernelScore b y - 1 / y)) y := by
    have harg : HasDerivAt (fun z => b * z) b y := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul b
    have hquot' : HasDerivAt (fun z => Real.sinh (b * z) / (b * z))
        ((Real.cosh (b * y) * b * (b * y) - Real.sinh (b * y) * b) /
          (b * y) ^ 2) y := by
      convert (((Real.hasDerivAt_sinh (b * y)).comp y harg).div harg (mul_ne_zero hb.ne' hy.ne')) using 1 <;> rfl
    change HasDerivAt (fun z : ℝ => Real.sinh (b * z) / (b * z))
      (conditionedKernelZeroParameterRatio b y *
        (conditionedKernelScore b y - 1 / y)) y
    convert hquot' using 1
    exact (show (Real.cosh (b * y) * b * (b * y) - Real.sinh (b * y) * b) / (b * y) ^ 2 = conditionedKernelZeroParameterRatio b y * (conditionedKernelScore b y - 1 / y) by dsimp [conditionedKernelZeroParameterRatio, conditionedKernelScore]; field_simp [hb.ne', hy.ne', (Real.sinh_pos_iff.mpr (mul_pos hb hy)).ne']).symm
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) (by change ContinuousOn (fun y => Real.sinh (b * y) / (b * y)) (Set.Ioi 0); apply (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).continuousOn.div (continuous_const.mul continuous_id).continuousOn; intro y hy; exact (mul_ne_zero hb.ne' (by simpa using ne_of_gt hy))) ?_ ?_
  · intro y hy
    exact (hasDerivAt_conditionedKernelZeroParameterRatio (by simpa using hy)).differentiableAt.differentiableWithinAt
  · intro y hy
    have hy' : 0 < y := by simpa using hy
    rw [(hasDerivAt_conditionedKernelZeroParameterRatio hy').deriv]
    exact mul_nonneg (le_of_lt (by simp only [conditionedKernelZeroParameterRatio]; exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hb hy')) (mul_pos hb hy')))
      (sub_nonneg.mpr (conditionedKernelScore_ge_reciprocal hb hy'))


/-- The entrance density likelihood ratio against zero drift is increasing in the endpoint. -/
theorem conditionedPositiveEntranceDensity_zero_ratio_monotoneOn_state
    {b t} (hb : 0 < b) (ht : 0 < t) :
    MonotoneOn
      (fun y => conditionedPositiveEntranceDensity b t y /
        conditionedPositiveEntranceDensity 0 t y) (Set.Ioi 0) := by
  have conditionedPositiveEntranceDensity_eq_zero_parameter_ratio_mul {y} (hy : 0 < y) : conditionedPositiveEntranceDensity b t y = Real.exp (-b ^ 2 * t / 2) * conditionedKernelZeroParameterRatio b y * conditionedPositiveEntranceDensity 0 t y := by
    simp [conditionedPositiveEntranceDensity, conditionedKernelZeroParameterRatio,
      hb.le, ht, hy, hb.ne']
    field_simp [hb.ne', hy.ne']
    rw [← Real.exp_add]
    calc
      t ^ (-(3 / 2 : ℝ)) *
          Real.exp ((-y ^ 2 - b ^ 2 * t ^ 2) / (2 * t)) * t ^ (3 / 2 : ℝ) =
        (t ^ (-(3 / 2 : ℝ)) * t ^ (3 / 2 : ℝ)) *
          Real.exp ((-y ^ 2 - b ^ 2 * t ^ 2) / (2 * t)) := by ring
      _ = Real.exp ((-y ^ 2 - b ^ 2 * t ^ 2) / (2 * t)) := by
        rw [mul_comm (t ^ (-(3 / 2 : ℝ))) (t ^ (3 / 2 : ℝ)), (show t ^ (3 / 2 : ℝ) * t ^ (-(3 / 2 : ℝ)) = 1 by rw [← Real.rpow_add ht]; norm_num)]
        ring
      _ = Real.exp (-(b ^ 2 * t / 2) + -(y ^ 2 / (2 * t))) := (by congr 1; field_simp [ht.ne']; ring)
  have hfactor y (hy : 0 < y) :
      conditionedPositiveEntranceDensity b t y /
        conditionedPositiveEntranceDensity 0 t y =
          Real.exp (-b ^ 2 * t / 2) * conditionedKernelZeroParameterRatio b y := by
    rw [conditionedPositiveEntranceDensity_eq_zero_parameter_ratio_mul hy]
    -- The zero-drift density is the Maxwell density and is strictly positive.
    field_simp [(show 0 < conditionedPositiveEntranceDensity 0 t y by simp [conditionedPositiveEntranceDensity, ht, hy]; positivity).ne']
  intro y₁ hy₁ y₂ hy₂ hy₁₂
  have hy₁' : 0 < y₁ := by simpa using hy₁
  have hy₂' : 0 < y₂ := by simpa using hy₂
  change conditionedPositiveEntranceDensity b t y₁ /
      conditionedPositiveEntranceDensity 0 t y₁ ≤
    conditionedPositiveEntranceDensity b t y₂ /
      conditionedPositiveEntranceDensity 0 t y₂
  rw [hfactor y₁ hy₁', hfactor y₂ hy₂']
  exact mul_le_mul_of_nonneg_left ((conditionedKernelZeroParameterRatio_monotoneOn_state hb) hy₁' hy₂' hy₁₂) (le_of_lt (Real.exp_pos _))


/-- The positive-to-zero-drift transition-kernel likelihood ratio is nondecreasing in the
endpoint. -/
theorem conditionedPositiveTransitionDensity_zero_ratio_monotoneOn_state
    {b t x} (hb : 0 < b) (ht : 0 < t) (hx : 0 < x) :
    MonotoneOn
      (fun y => conditionedPositiveTransitionDensity b t x y /
        conditionedPositiveTransitionDensity 0 t x y) (Set.Ioi 0) := by
  have conditionedPositiveTransitionDensity_eq_zero_parameter_ratio_mul {y} (hy : 0 < y) : conditionedPositiveTransitionDensity b t x y = (Real.exp (-b ^ 2 * t / 2) * (b * x / Real.sinh (b * x))) * conditionedKernelZeroParameterRatio b y * conditionedPositiveTransitionDensity 0 t x y := by
    simp [conditionedPositiveTransitionDensity, conditionedH,
      conditionedKernelZeroParameterRatio, hb.le, ht, hx, hy, hb.ne']
    rw [show -(2 * b * y) = -2 * (b * y) by ring, (one_sub_exp_neg_two_mul_eq_two_exp_neg_mul_sinh (b * y)),
      show -(2 * b * x) = -2 * (b * x) by ring, (one_sub_exp_neg_two_mul_eq_two_exp_neg_mul_sinh (b * x))]
    field_simp [hb.ne', hx.ne', hy.ne', (Real.sinh_pos_iff.mpr (mul_pos hb hx)).ne', (Real.sinh_pos_iff.mpr (mul_pos hb hy)).ne', (brownianHeatDensity_sub_pos ht hx hy).ne']
    conv_lhs => rw [← Real.exp_add]
    conv_rhs => rw [← Real.exp_add]
    congr 1
    ring
  have hfactor y (hy : 0 < y) :
      conditionedPositiveTransitionDensity b t x y /
        conditionedPositiveTransitionDensity 0 t x y =
          (Real.exp (-b ^ 2 * t / 2) * (b * x / Real.sinh (b * x))) *
            conditionedKernelZeroParameterRatio b y := by
    rw [conditionedPositiveTransitionDensity_eq_zero_parameter_ratio_mul hy]
    field_simp [(show 0 < conditionedPositiveTransitionDensity 0 t x y by simp [conditionedPositiveTransitionDensity, conditionedH, ht, hx, hy]; exact sub_pos.mp (brownianHeatDensity_sub_pos ht hx hy)).ne']
  intro y₁ hy₁ y₂ hy₂ hy₁₂
  have hy₁' : 0 < y₁ := by simpa using hy₁
  have hy₂' : 0 < y₂ := by simpa using hy₂
  change conditionedPositiveTransitionDensity b t x y₁ /
      conditionedPositiveTransitionDensity 0 t x y₁ ≤
    conditionedPositiveTransitionDensity b t x y₂ /
      conditionedPositiveTransitionDensity 0 t x y₂
  rw [hfactor y₁ hy₁', hfactor y₂ hy₂']
  exact mul_le_mul_of_nonneg_left ((conditionedKernelZeroParameterRatio_monotoneOn_state hb) hy₁' hy₂' hy₁₂) (le_of_lt (mul_pos (Real.exp_pos _) (div_pos (mul_pos hb hx) (Real.sinh_pos_iff.mpr (mul_pos hb hx)))))

end DOZZ.Proofs

end
