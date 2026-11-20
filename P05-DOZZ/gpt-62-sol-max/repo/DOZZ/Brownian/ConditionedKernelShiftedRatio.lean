/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelScoreParameter
public import DOZZ.Brownian.ConditionedKernelParameterRatio
public import DOZZ.Brownian.ConditionedKernelCDFOrder
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Upper stochastic order for shifted conditioned Brownian kernels, including zero drift. -/

@[expose] public section
open MeasureTheory Topology Set
namespace DOZZ.Proofs

/-- For strictly positive drift, the transition density's endpoint dependence is a fixed positive
factor times its Gaussian and two hyperbolic-sine factors. -/
theorem conditionedPositiveTransitionDensity_eq_sinh_gaussian_factor
    {ν t x y : ℝ} (hν : 0 < ν) (ht : 0 < t) (hx : 0 < x) (hy : 0 < y) :
    conditionedPositiveTransitionDensity ν t x y =
      (2 * Real.exp (-ν ^ 2 * t / 2 - x ^ 2 / (2 * t)) /
        (Real.sqrt (2 * Real.pi * t) * Real.sinh (ν * x))) *
        (Real.exp (-y ^ 2 / (2 * t)) * Real.sinh (ν * y) * Real.sinh (x * y / t)) := by
  have hheat := brownianHeatDensity_sub_factor ht (x := x) (y := y)
  have hHνy := conditionedH_eq_sinh (x := y) hν
  have hHνx := conditionedH_eq_sinh (x := x) hν
  have hsinhX  :=
    Real.sinh_pos_iff.mpr (div_pos (mul_pos hx hy) ht)
  have hsinhνx  :=
    Real.sinh_pos_iff.mpr (mul_pos hν hx)
  have hroot : 0 < Real.sqrt (2 * Real.pi * t) := by positivity
  simp [conditionedPositiveTransitionDensity, hν.le, ht, hx, hy,
    hheat, hHνy, hHνx]
  field_simp [hroot.ne', hsinhνx.ne']
  conv_lhs => rw [← Real.exp_add, ← Real.exp_add]
  conv_rhs => rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_injective
  field_simp [ht.ne']
  ring_nf

theorem conditionedPositiveTransitionDensity_zero_eq_sinh_gaussian_factor
    {t x y : ℝ} (ht : 0 < t) (hx : 0 < x) (hy : 0 < y) :
    conditionedPositiveTransitionDensity 0 t x y =
      (2 * Real.exp (-x ^ 2 / (2 * t)) /
        (Real.sqrt (2 * Real.pi * t) * x)) *
        (Real.exp (-y ^ 2 / (2 * t)) * y * Real.sinh (x / t * y)) := by
  have hheat := brownianHeatDensity_sub_factor ht (x := x) (y := y)
  have hsqrt : Real.sqrt (2 * Real.pi * t) ≠ 0 := by positivity
  simp [conditionedPositiveTransitionDensity, conditionedH, ht, hx, hy]
  rw [hheat]
  have hexp : Real.exp (-(x ^ 2 + y ^ 2) / (2 * t)) =
      Real.exp (-x ^ 2 / (2 * t)) * Real.exp (-y ^ 2 / (2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp [ht.ne']
    ring_nf
  rw [hexp]
  have harg : x * y / t = x / t * y := by ring
  rw [harg]
  field_simp [hx.ne', hsqrt]

/-- The endpoint factor at zero drift is linear instead of hyperbolic. -/
noncomputable def conditionedShape (c y : ℝ) : ℝ :=
  if c = 0 then y else Real.sinh (c * y)

private noncomputable def conditionedShapeScore (c y : ℝ) : ℝ :=
  if c = 0 then 1 / y else conditionedKernelScore c y

section
variable {c y : ℝ} (hc : 0 ≤ c) (hy : 0 < y)
include hc hy

private theorem conditionedShape_pos :
    0 < conditionedShape c y := by
  rcases hc.eq_or_lt with h | h
  · simpa [conditionedShape, ← h] using hy
  · simp [conditionedShape, h.ne', Real.sinh_pos_iff, mul_pos h hy]

private theorem hasDerivAt_conditionedShape :
    HasDerivAt (conditionedShape c) (conditionedShape c y * conditionedShapeScore c y) y := by
  rcases hc.eq_or_lt with h | h
  · subst c
    have h : conditionedShape 0 = id := funext (by simp [conditionedShape, id])
    simpa [h, conditionedShapeScore, hy.ne'] using hasDerivAt_id y
  · simp only [conditionedShape, conditionedShapeScore, h.ne', ite_false]
    convert ((hasDerivAt_id y).const_mul c).sinh using 1
    · funext z
      simp [conditionedShape, h.ne']
    · unfold conditionedKernelScore
      field_simp [(Real.sinh_pos_iff.mpr (mul_pos h hy)).ne'] <;> rfl

end

private theorem conditionedShapeScore_increment {a b y z : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hy : 0 < y) (hyz : y ≤ z) :
    conditionedShapeScore b z - conditionedShapeScore a y ≤ b - a := by
  have hz := hy.trans_le hyz
  rcases ha.eq_or_lt with ha | ha
  · subst a
    rcases hab.eq_or_lt with hb | hb
    · subst b
      simpa [conditionedShapeScore, sub_nonpos] using one_div_le_one_div_of_le hy hyz
    · have hs := (conditionedKernelScore_strictAntiOn_state hb).antitoneOn hy hz hyz
      have h := (conditionedKernelScore_zero_increment_bounds hb hy).2
      simp only [conditionedShapeScore, hb.ne', ite_false, ite_true, sub_zero]
      linarith
  · simpa only [conditionedShapeScore, ha.ne', (ha.trans_le hab).ne', ite_false] using
      conditionedKernelScore_mixed_increment_upper ha hy hyz hab

private theorem hasDerivAt_quotient_of_scores {f g : ℝ → ℝ} {y a b : ℝ}
    (hf : HasDerivAt f (f y * a) y) (hg : HasDerivAt g (g y * b) y) (hg₀ : g y ≠ 0) :
    HasDerivAt (fun u => f u / g u) ((f y / g y) * (a - b)) y := by
  convert hf.div hg hg₀ using 1
  field_simp [hg₀]

noncomputable def shiftedShapeRatio (a b d y : ℝ) : ℝ :=
  conditionedShape b (y + d) / conditionedShape a y

private theorem hasDerivAt_shiftedShapeRatio {a b d y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hy : 0 < y) (hd : 0 ≤ d) :
    HasDerivAt (shiftedShapeRatio a b d) (shiftedShapeRatio a b d y *
      (conditionedShapeScore b (y + d) - conditionedShapeScore a y)) y := by
  have hf := (hasDerivAt_conditionedShape hb (add_pos_of_pos_of_nonneg hy hd)).comp y
    ((hasDerivAt_id y).add_const d)
  have hg := hasDerivAt_conditionedShape ha hy
  exact hasDerivAt_quotient_of_scores (by simpa only [Function.comp_def, id_eq, mul_one] using hf)
    hg (conditionedShape_pos ha hy).ne'

/-- The state-dependent part of the density ratio, after shifting the endpoint by `d`.
The two shapes come from the drift and from the scaled starting position. -/
noncomputable def conditionedShiftRatio (a b c c' t d y : ℝ) : ℝ :=
  Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
    shiftedShapeRatio a b d y * shiftedShapeRatio c c' d y

private theorem hasDerivAt_conditionedShiftRatio {a b c c' t d y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hc' : 0 ≤ c') (hd : 0 ≤ d) (hy : 0 < y) :
    HasDerivAt (conditionedShiftRatio a b c c' t d)
      (conditionedShiftRatio a b c c' t d y * (-(d / t) +
        (conditionedShapeScore b (y + d) - conditionedShapeScore a y) +
        (conditionedShapeScore c' (y + d) - conditionedShapeScore c y))) y := by
  have hE := (((hasDerivAt_id y).const_mul (-(d / t))).sub_const (d ^ 2 / (2 * t))).exp
  have h₁ := hasDerivAt_shiftedShapeRatio ha hb hy hd
  have h₂ := hasDerivAt_shiftedShapeRatio hc hc' hy hd
  convert (hE.mul h₁).mul h₂ using 1
  · rfl
  · simp only [conditionedShiftRatio, Pi.mul_apply, id_eq, mul_one]
    ring

/-- A shift that compensates the two parameter increments makes the ratio antitone. -/
theorem conditionedShiftRatio_antitoneOn {a b c c' t d : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hcc' : c ≤ c') (hd : 0 ≤ d)
    (hshift : b - a + (c' - c) ≤ d / t) :
    AntitoneOn (conditionedShiftRatio a b c c' t d) (Ioi 0) := by
  have hb := ha.trans hab
  have hc' := hc.trans hcc'
  have hD {y : ℝ} (hy : 0 < y) := hasDerivAt_conditionedShiftRatio
    (t := t) ha hb hc hc' hd hy
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (fun _ hy => (hD hy).continuousAt.continuousWithinAt) ?_ ?_
  · intro y hy
    exact (hD (by simpa only [interior_Ioi, mem_Ioi] using hy)).differentiableAt.differentiableWithinAt
  · intro y hy
    have hy₀ : 0 < y := by simpa only [interior_Ioi, mem_Ioi] using hy
    have hyD := add_pos_of_pos_of_nonneg hy₀ hd
    rw [(hD hy₀).deriv]
    refine mul_nonpos_of_nonneg_of_nonpos ?_ ?_
    · have h₁ := conditionedShape_pos ha hy₀
      have h₂ := conditionedShape_pos hb hyD
      have h₃ := conditionedShape_pos hc hy₀
      have h₄ := conditionedShape_pos hc' hyD
      unfold conditionedShiftRatio shiftedShapeRatio
      positivity
    · have h₁ := conditionedShapeScore_increment ha hab hy₀ (le_add_of_nonneg_right hd)
      have h₂ := conditionedShapeScore_increment hc hcc' hy₀ (le_add_of_nonneg_right hd)
      linarith

private theorem conditionedTransitionDensity_shape {a t x y : ℝ}
    (ha : 0 ≤ a) (ht : 0 < t) (hx : 0 < x) (hy : 0 < y) :
    conditionedPositiveTransitionDensity a t x y =
      (2 * Real.exp (-a ^ 2 * t / 2 - x ^ 2 / (2 * t)) /
        (Real.sqrt (2 * Real.pi * t) * conditionedShape a x)) *
        (Real.exp (-y ^ 2 / (2 * t)) * conditionedShape a y * conditionedShape (x / t) y) := by
  have hxt := (div_pos hx ht).ne'
  rcases ha.eq_or_lt with ha | ha
  · subst a
    simpa [conditionedShape, hxt, neg_div] using conditionedPositiveTransitionDensity_zero_eq_sinh_gaussian_factor ht hx hy
  · simpa [conditionedShape, ha.ne', hxt, div_mul_eq_mul_div] using
      conditionedPositiveTransitionDensity_eq_sinh_gaussian_factor ha ht hx hy

/-- Endpoint-independent normalization in the shifted density identity. -/
noncomputable def conditionedShiftScale (a b t x' x : ℝ) : ℝ :=
  Real.exp ((a ^ 2 - b ^ 2) * t / 2 + (x' ^ 2 - x ^ 2) / (2 * t)) *
    (conditionedShape a x' / conditionedShape b x)

theorem conditionedShiftScale_nonneg {a b t x' x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx' : 0 < x') (hx : 0 < x) : 0 ≤ conditionedShiftScale a b t x' x :=
  mul_nonneg (Real.exp_pos _).le (div_nonneg (conditionedShape_pos ha hx').le (conditionedShape_pos hb hx).le)

theorem conditionedTransitionDensity_shift_eq {a b t x' x d y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t) (hx' : 0 < x') (hx : 0 < x)
    (hd : 0 ≤ d) (hy : 0 < y) :
    conditionedPositiveTransitionDensity b t x (y + d) =
      conditionedShiftScale a b t x' x * conditionedShiftRatio a b (x' / t) (x / t) t d y *
        conditionedPositiveTransitionDensity a t x' y := by
  have he : Real.exp (-(y + d) ^ 2 / (2 * t)) =
      Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) * Real.exp (-y ^ 2 / (2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE : Real.exp (-b ^ 2 * t / 2 - x ^ 2 / (2 * t)) =
      Real.exp ((a ^ 2 - b ^ 2) * t / 2 + (x' ^ 2 - x ^ 2) / (2 * t)) *
        Real.exp (-a ^ 2 * t / 2 - x' ^ 2 / (2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [conditionedTransitionDensity_shape hb ht hx (add_pos_of_pos_of_nonneg hy hd),
    conditionedTransitionDensity_shape ha ht hx' hy, he, hE]
  unfold conditionedShiftScale conditionedShiftRatio shiftedShapeRatio
  field_simp [(conditionedShape_pos ha hx').ne', (conditionedShape_pos ha hy).ne',
    (conditionedShape_pos (div_nonneg hx'.le ht.le) hy).ne']
  <;> ring

end DOZZ.Proofs
