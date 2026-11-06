/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.LaplaceTail
public import DOZZ.GMC.SharpMoments.ReverseJensen

/-! # Gaussian decay of cutoff Laplace transforms at bounded cutoff

At a cutoff in a bounded range, the circle variance on a reference ball is bounded uniformly by the
chart constant, so every inverse moment of the cutoff mass has Gaussian growth in the order. The
Chernoff bound turns this into a Gaussian small-value tail, which gives Gaussian decay in the
logarithmic level of the Laplace transform of the cutoff mass, with constants uniform in the
cutoff. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-! ### Real-variable estimates -/

/-- The double exponential `exp (-exp (x / 2))` has Gaussian decay, since `exp y ≥ y ^ 2 / 2`. -/
theorem laplaceBase_exp_neg_exp_half_le {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-Real.exp (x / 2)) ≤ Real.exp (-(x ^ 2 / 8)) := by
  refine Real.exp_le_exp.mpr ?_
  have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ x / 2 by linarith)
  linarith

/-- A shifted Gaussian is bounded by a constant multiple of a Gaussian of smaller variance. -/
theorem laplaceBase_gaussian_shift_le {b : ℝ} (hb : 0 < b) (a x : ℝ) :
    Real.exp (-(x / 2 - a) ^ 2 / (4 * b)) ≤
      Real.exp (a ^ 2 / (4 * b)) * Real.exp (-(x ^ 2 / (32 * b))) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h : a ^ 2 / (4 * b) + -(x ^ 2 / (32 * b)) - (-(x / 2 - a) ^ 2 / (4 * b)) =
      (x - 4 * a) ^ 2 / (32 * b) := by
    ring
  have h2 : 0 ≤ (x - 4 * a) ^ 2 / (32 * b) := by positivity
  linarith

/-- Real-variable core. For `b > 0` there are constants `A` and `c > 0`, depending only on `a` and
`b`, such that every `L ≤ 1` which is at most the Gaussian tail
`exp (-(x / 2 - a) ^ 2 / (4 * b))` plus the double exponential `exp (-exp (x / 2))` whenever
`a < x / 2` satisfies `L ≤ A * exp (-c * x ^ 2)` for all `x ≥ 0`. -/
theorem laplaceBase_real_core (a b : ℝ) (hb : 0 < b) :
    ∃ A c : ℝ, 0 < c ∧ ∀ L x : ℝ, 0 ≤ x → L ≤ 1 →
      (a < x / 2 → L ≤ Real.exp (-(x / 2 - a) ^ 2 / (4 * b)) + Real.exp (-Real.exp (x / 2))) →
      L ≤ A * Real.exp (-c * x ^ 2) := by
  have hb32 : 0 < 1 / (32 * b) := by positivity
  set c := min (1 / (32 * b)) (1 / 8)
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 / (32 * b) := min_le_left ..
  have hc2 : c ≤ 1 / 8 := min_le_right ..
  refine ⟨Real.exp (a ^ 2 / (4 * b)) + 1 + Real.exp (c * (2 * a) ^ 2), c, hc0,
    fun L x hx hL h => ?_⟩
  set E := Real.exp (-c * x ^ 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  by_cases hax : a < x / 2
  · have h1 := h hax
    have h2 := laplaceBase_gaussian_shift_le hb a x
    have h3 := laplaceBase_exp_neg_exp_half_le hx
    have h4 : Real.exp (-(x ^ 2 / (32 * b))) ≤ E := by
      refine Real.exp_le_exp.mpr ?_
      have hmul := mul_le_mul_of_nonneg_right hc1 (sq_nonneg x)
      have e : 1 / (32 * b) * x ^ 2 = x ^ 2 / (32 * b) := by ring
      linarith
    have h5 : Real.exp (-(x ^ 2 / 8)) ≤ E := by
      refine Real.exp_le_exp.mpr ?_
      have hmul := mul_le_mul_of_nonneg_right hc2 (sq_nonneg x)
      have e : 1 / 8 * x ^ 2 = x ^ 2 / 8 := by ring
      linarith
    have h6 : Real.exp (a ^ 2 / (4 * b)) * Real.exp (-(x ^ 2 / (32 * b))) ≤
        Real.exp _ * E :=
      mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
    have h7 : 0 ≤ Real.exp (c * (2 * a) ^ 2) * E := (mul_pos (Real.exp_pos _) hE0).le
    linarith
  · have hxa : x ≤ 2 * a := by linarith
    have hx2 : x ^ 2 ≤ (2 * a) ^ 2 := pow_le_pow_left₀ hx hxa 2
    have h1 : 1 ≤ Real.exp (c * (2 * a) ^ 2) * E := by
      rw [hE, ← Real.exp_add]
      apply Real.one_le_exp
      have hmul := mul_nonneg hc0.le (sub_nonneg.mpr hx2)
      linarith
    have h2 : 0 ≤ Real.exp (a ^ 2 / (4 * b)) * E := (mul_pos (Real.exp_pos _) hE0).le
    calc L ≤ 1 := hL
      _ ≤ Real.exp _ * E := h1
      _ ≤ (Real.exp _ + 1 + Real.exp _) * E := by linarith
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-! ### From small-value tails to the Laplace transform -/

/-- A nonnegative variable `m` has Laplace transform at level `exp x` at most the probability that
`m ≤ exp (-(x / 2))` plus the double exponential `exp (-exp (x / 2))`. -/
theorem laplaceBase_integral_le_measureReal_add
    [IsProbabilityMeasure P]
    (m : Ω → ℝ) (hm : Measurable m) (hm0 : ∀ ω, 0 ≤ m ω) (x : ℝ) :
    ∫ ω, Real.exp (-(Real.exp x) * m ω) ∂P ≤
      P.real {ω | m ω ≤ Real.exp (-(x / 2))} + Real.exp (-Real.exp (x / 2)) := by
  have hset : MeasurableSet {ω | m ω ≤ Real.exp (-(x / 2))} :=
    measurableSet_le hm measurable_const
  have hint : Integrable (fun ω => Real.exp (-(Real.exp x) * m ω)) P := by
    refine Integrable.of_bound (C := 1) (Real.measurable_exp.comp
      (hm.const_mul _)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact cutoffLaplace_integrand_le_one _ _ (Real.exp_pos x).le (hm0 ω)
  have hind : Integrable ({ω | m ω ≤ Real.exp (-(x / 2))}.indicator (1 : Ω → ℝ)) P :=
    (integrable_const 1).indicator hset
  have hpoint : ∀ ω, Real.exp (-(Real.exp x) * m ω) ≤
      {ω | m ω ≤ Real.exp (-(x / 2))}.indicator (1 : Ω → ℝ) ω + Real.exp (-Real.exp (x / 2)) := by
    intro ω
    have hpos : 0 < Real.exp (-Real.exp (x / 2)) := Real.exp_pos _
    by_cases hω : m ω ≤ Real.exp (-(x / 2))
    · rw [Set.indicator_of_mem (show ω ∈ {ω | m ω ≤ Real.exp (-(x / 2))} from hω), Pi.one_apply]
      have h1 := cutoffLaplace_integrand_le_one _ _ (Real.exp_pos x).le (hm0 ω)
      linarith
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | m ω ≤ Real.exp (-(x / 2))} from hω), zero_add]
      refine Real.exp_le_exp.mpr ?_
      have hmul :=
        mul_lt_mul_of_pos_left (not_le.mp hω) (Real.exp_pos x)
      rw [← Real.exp_add, show x + -(x / 2) = x / 2 by ring] at hmul
      linarith
  calc ∫ ω, Real.exp _ ∂P
      ≤ ∫ ω, ({ω | m ω ≤ Real.exp _}.indicator 1 ω +
          Real.exp _) ∂P :=
        integral_mono hint (hind.add (integrable_const _)) hpoint
    _ = P.real {ω | m ω ≤ Real.exp _} + Real.exp _ := by
        rw [integral_add hind (integrable_const _), integral_indicator_one hset]
        simp

/-- For an almost surely finite `Y`, the event that the real part is at most `ε` is almost
surely contained in the event `Y ≤ ofReal ε`. -/
theorem laplaceBase_measure_toReal_le
    (Y : Ω → ℝ≥0∞) (hY : ∀ᵐ ω ∂P, Y ω ≠ ⊤)
    (ε : ℝ) (hε : 0 ≤ ε) :
    P {ω | (Y ω).toReal ≤ ε} ≤ P {ω | Y ω ≤ ENNReal.ofReal ε} := by
  refine measure_mono_ae ?_
  filter_upwards [hY] with ω hω h
  exact (ENNReal.le_ofReal_iff_toReal_le hω hε).mpr h
section
variable (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
include hX hXc

/-- Gaussian-type negative moments of the cutoff mass of `A` bound its Laplace transform at level
`exp x`, once `a < x / 2`, by the Chernoff small-value tail plus the double exponential. -/
theorem laplaceBase_cutoffLaplace_le_of_negMoment
    (γ r : ℝ)
    (A : Set ℂ) (hA : MeasurableSet A) (a b : ℝ) (hb : 0 < b)
    (hmom : ∀ q : ℝ, 0 < q → ∫⁻ ω, (regularizedGMC P Xc γ r ω A) ^ (-q) ∂P ≤
      ENNReal.ofReal (Real.exp (a * q + b * q ^ 2)))
    (x : ℝ) (hx : a < x / 2) :
    cutoffLaplace P Xc γ r A x ≤
      Real.exp (-(x / 2 - a) ^ 2 / (4 * b)) + Real.exp (-Real.exp (x / 2)) := by
  have hP := hX.1
  have hYm :=
    (Measure.measurable_coe hA).comp (regularizedGMC_measurable P X hX Xc hXc γ r)
  have hLaplace := laplaceBase_integral_le_measureReal_add P _
    (measurable_regularizedGMC_apply_toReal P X hX Xc hXc γ r A hA)
    (fun _ => ENNReal.toReal_nonneg) x
  have hae : ∀ᵐ ω ∂P, regularizedGMC P Xc γ r ω A ≠ ⊤ := by
    filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ r] with ω hω
    simp
  have htail : P.real {ω | (regularizedGMC P Xc γ r ω A).toReal ≤ Real.exp (-(x / 2))} ≤
      Real.exp (-(x / 2 - a) ^ 2 / (4 * b)) := by
    rw [measureReal_def]
    calc _ ≤ (ENNReal.ofReal _).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top ((laplaceBase_measure_toReal_le P _ hae (Real.exp (-(x / 2))) (Real.exp_pos _).le).trans (measure_le_exp_neg_of_negMoment P _ hYm.aemeasurable a b hb hmom (x / 2) hx))
      _ = _ := ENNReal.toReal_ofReal (Real.exp_pos _).le
  unfold cutoffLaplace
  linarith

/-- On a set of positive finite reference mass where the circle variance is at most `V`, the
inverse moments of the cutoff mass have Gaussian growth in the order, with linear coefficient
`b - log σ` and quadratic coefficient `b`, where `b = γ² V / 2` and `σ` is the reference mass. -/
theorem laplaceBase_negMoment_le
    (γ r V : ℝ)
    (A : Set ℂ) (hA : MeasurableSet A) (hA0 : gmcReferenceMeasure A ≠ 0)
    (hAtop : gmcReferenceMeasure A ≠ ⊤)
    (hV : ∀ x ∈ A, gaussianVariance P (fun ω => Xc ω x r) ≤ V) (a b : ℝ)
    (hb : b = γ ^ 2 * V / 2) (ha : a = b - Real.log (gmcReferenceMeasure A).toReal)
    (q : ℝ) (hq : 0 < q) :
    ∫⁻ ω, (regularizedGMC P Xc γ r ω A) ^ (-q) ∂P ≤
      ENNReal.ofReal (Real.exp (a * q + b * q ^ 2)) := by
  refine (regularizedGMC_inverse_moment_le_variance P X hX Xc hXc γ r q V hq A hA hA0 hAtop
    hV).trans (le_of_eq ?_)
  have hσ := ENNReal.toReal_pos hA0 hAtop
  rw [← ENNReal.ofReal_toReal hAtop, ENNReal.ofReal_rpow_of_pos hσ,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hσ.le _), Real.rpow_def_of_pos hσ, ← Real.exp_add]
  grind

end

end

/-! ### The reference ball -/

/-- A ball in the unit chart has positive reference mass. This is the statement of
`gmc_reference_ball_intensity_pos`, reproved from `gmcReferenceMeasure_restrict_unit_chart` so that
this module does not import `ReferenceIntensity`. -/
theorem laplaceBase_ball_pos {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) :
    0 < gmcReferenceMeasure (Metric.ball (0 : ℂ) R) := by
  have he := gmcReferenceMeasure_restrict_unit_chart _
    Metric.isOpen_ball.measurableSet fun x hx => (mem_ball_zero_iff.mp hx).le.trans hR1
  have hv := congrArg (fun μ => μ Set.univ) he
  simp only [Measure.restrict_apply_univ] at hv
  rw [hv]
  exact Metric.measure_ball_pos volume 0 hR

/-- A ball has finite reference mass. -/
theorem laplaceBase_ball_ne_top (R : ℝ) :
    gmcReferenceMeasure (Metric.ball (0 : ℂ) R) ≠ ⊤ :=
  ne_top_of_le_ne_top gmcReferenceMeasure_univ_ne_top (measure_mono (Set.subset_univ _))

/-- The chart remainder is strictly positive on a positive radius. -/
theorem laplaceBase_chartRemainder_pos {R : ℝ} (hR : 0 < R) :
    0 < gmcCircleChartRemainder R :=
  add_pos_of_pos_of_nonneg (Real.log_pos (by norm_num))
    (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))

/-- At cutoffs in a bounded range, the Laplace transform of a reference-ball mass has Gaussian
decay in the logarithmic level, uniformly in the cutoff. -/
theorem cutoffLaplace_le_gaussian_bounded_cutoff
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ) (hγ : 0 < γ)
    (R T : ℝ) (hR : 0 < R) (hR1 : R ≤ 1) (hT : 0 ≤ T) :
    ∃ A c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 ≤ r → r ≤ T → ∀ x : ℝ, 0 ≤ x →
      cutoffLaplace P Xc γ r (Metric.ball 0 R) x ≤ A * Real.exp (-c * x ^ 2) := by
  have hDm : MeasurableSet (Metric.ball (0 : ℂ) R) := Metric.isOpen_ball.measurableSet
  have hD0 :=
    (laplaceBase_ball_pos hR hR1).ne'
  have hVpos :=
    add_pos_of_nonneg_of_pos hT (laplaceBase_chartRemainder_pos hR)
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = γ ^ 2 * (T + gmcCircleChartRemainder R) / 2 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ,
      a = b - Real.log (gmcReferenceMeasure (Metric.ball 0 R)).toReal := ⟨_, rfl⟩
  have hbpos : 0 < b := by
    simp_all
  obtain ⟨A, c, hc, hcore⟩ := laplaceBase_real_core a b hbpos
  refine ⟨A, c, hc, fun r hr0 hrT x hx0 => ?_⟩
  have hvar : ∀ y ∈ Metric.ball 0 R,
      gaussianVariance P (fun ω => Xc ω y r) ≤ T + gmcCircleChartRemainder R := fun y hy =>
    gmcCircle_variance_le_coarse_chart P X hX Xc hXc R r T hR.le hr0 hrT y
      (mem_ball_zero_iff.mp hy).le
  have hmom : ∀ q : ℝ, 0 < q →
      ∫⁻ ω, (regularizedGMC P Xc γ r ω _) ^ (-q) ∂P ≤
        ENNReal.ofReal _ := fun q hq =>
    laplaceBase_negMoment_le P X hX Xc hXc γ r _ _ hDm hD0 (laplaceBase_ball_ne_top R) hvar a b hb ha q hq
  exact hcore _ x hx0 (cutoffLaplace_le_one P X hX Xc γ r _ x) fun hax =>
    laplaceBase_cutoffLaplace_le_of_negMoment P X hX Xc hXc γ r _ hDm a b hbpos hmom x hax

end DOZZ.Proofs
