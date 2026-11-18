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

variable {Ω : Type*} [MeasurableSpace Ω]


/-! ### Real-variable estimates -/




/-! ### From small-value tails to the Laplace transform -/





/-! ### The reference ball -/


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

    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ) (hγ : 0 < γ)
    (R T : ℝ) (hR : 0 < R) (hR1 : R ≤ 1) (hT : 0 ≤ T) :
    ∃ A c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 ≤ r → r ≤ T → ∀ x : ℝ, 0 ≤ x →
      cutoffLaplace P Xc γ r (Metric.ball 0 R) x ≤ A * Real.exp (-c * x ^ 2) := by
  have laplaceBase_ball_pos : 0 < gmcReferenceMeasure (Metric.ball (0 : ℂ) R) := by
    have he := gmcReferenceMeasure_restrict_unit_chart (Metric.ball (0 : ℂ) R)
      Metric.isOpen_ball.measurableSet fun x hx => (mem_ball_zero_iff.mp hx).le.trans hR1
    have hv := congrArg (fun μ : Measure ℂ => μ Set.univ) he
    simp only [Measure.restrict_apply_univ] at hv
    rw [hv]
    exact Metric.measure_ball_pos volume 0 hR
  have laplaceBase_cutoffLaplace_le_of_negMoment (r : ℝ) (A : Set ℂ) (hA : MeasurableSet A) (a b : ℝ) (hb : 0 < b) (hmom : ∀ q : ℝ, 0 < q → ∫⁻ ω, (regularizedGMC P Xc γ r ω A) ^ (-q) ∂P ≤ ENNReal.ofReal (Real.exp (a * q + b * q ^ 2))) (x : ℝ) (hx : a < x / 2) : cutoffLaplace P Xc γ r A x ≤
        Real.exp (-(x / 2 - a) ^ 2 / (4 * b)) + Real.exp (-Real.exp (x / 2)) := by
    have laplaceBase_measure_toReal_le (Y : Ω → ℝ≥0∞) (hY : ∀ᵐ ω ∂P, Y ω ≠ ⊤) (ε : ℝ) (hε : 0 ≤ ε) : P {ω | (Y ω).toReal ≤ ε} ≤ P {ω | Y ω ≤ ENNReal.ofReal ε} := by
      refine measure_mono_ae ?_
      filter_upwards [hY] with ω hω h
      exact (ENNReal.le_ofReal_iff_toReal_le hω hε).mpr h
    have laplaceBase_integral_le_measureReal_add [IsProbabilityMeasure P] (m : Ω → ℝ) (hm : Measurable m) (hm0 : ∀ ω, 0 ≤ m ω) (x : ℝ) : ∫ ω, Real.exp (-(Real.exp x) * m ω) ∂P ≤
          P.real {ω | m ω ≤ Real.exp (-(x / 2))} + Real.exp (-Real.exp (x / 2)) := by
      have hset : MeasurableSet {ω | m ω ≤ Real.exp (-(x / 2))} :=
        measurableSet_le hm measurable_const
      have hint : Integrable (fun ω => Real.exp (-(Real.exp x) * m ω)) P := by
        refine Integrable.of_bound (C := 1) (Real.measurable_exp.comp
          (hm.const_mul _)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact cutoffLaplace_integrand_le_one _ _ (Real.exp_pos x).le (hm0 ω)
      have hind : Integrable ({ω | m ω ≤ Real.exp (-(x / 2))}.indicator (1 : Ω → ℝ)) P :=
        (integrable_const (1 : ℝ)).indicator hset
      have hpoint : ∀ ω, Real.exp (-(Real.exp x) * m ω) ≤
          {ω | m ω ≤ Real.exp (-(x / 2))}.indicator (1 : Ω → ℝ) ω + Real.exp (-Real.exp (x / 2)) := by
        intro ω
        have : 0 < Real.exp (-Real.exp (x / 2)) := Real.exp_pos _
        by_cases hω : m ω ≤ Real.exp (-(x / 2))
        · rw [Set.indicator_of_mem (show ω ∈ {ω | m ω ≤ Real.exp (-(x / 2))} from hω), Pi.one_apply]
          have := cutoffLaplace_integrand_le_one _ _ (Real.exp_pos x).le (hm0 ω)
          linarith
        · rw [Set.indicator_of_notMem (show ω ∉ {ω | m ω ≤ Real.exp (-(x / 2))} from hω), zero_add]
          refine Real.exp_le_exp.mpr ?_
          have hmul :=
            mul_lt_mul_of_pos_left (not_le.mp hω) (Real.exp_pos x)
          rw [← Real.exp_add, show x + -(x / 2) = x / 2 by ring] at hmul
          linarith
      calc ∫ ω, Real.exp (-(Real.exp x) * m ω) ∂P
          ≤ ∫ ω, ({ω | m ω ≤ Real.exp (-(x / 2))}.indicator (1 : Ω → ℝ) ω +
              Real.exp (-Real.exp (x / 2))) ∂P :=
            integral_mono hint (hind.add (integrable_const _)) hpoint
        _ = P.real {ω | m ω ≤ Real.exp (-(x / 2))} + Real.exp (-Real.exp (x / 2)) := by
            rw [integral_add hind (integrable_const _), integral_indicator_one hset]
            simp
    have := hX.1
    have := laplaceBase_integral_le_measureReal_add _
      (measurable_regularizedGMC_apply_toReal P X hX Xc hXc γ r A hA)
      (fun _ => ENNReal.toReal_nonneg) x
    have hae : ∀ᵐ ω ∂P, regularizedGMC P Xc γ r ω A ≠ ⊤ := by
      filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ r] with ω hω
      exact measure_ne_top _ _
    have : P.real {ω | (regularizedGMC P Xc γ r ω A).toReal ≤ Real.exp (-(x / 2))} ≤
        Real.exp (-(x / 2 - a) ^ 2 / (4 * b)) := by
      rw [measureReal_def]
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top ((laplaceBase_measure_toReal_le _ hae (Real.exp (-(x / 2))) (Real.exp_pos _).le).trans (measure_le_exp_neg_of_negMoment P _ ((Measure.measurable_coe hA).comp (regularizedGMC_measurable P X hX Xc hXc γ r)).aemeasurable a b hb hmom (x / 2) hx))).trans_eq (ENNReal.toReal_ofReal (Real.exp_pos _).le)
    unfold cutoffLaplace
    linarith
  have laplaceBase_real_core (a b : ℝ) (hb : 0 < b) : ∃ A c : ℝ, 0 < c ∧ ∀ L x : ℝ, 0 ≤ x → L ≤ 1 →
        (a < x / 2 → L ≤ Real.exp (-(x / 2 - a) ^ 2 / (4 * b)) + Real.exp (-Real.exp (x / 2))) →
        L ≤ A * Real.exp (-c * x ^ 2) := by
    have laplaceBase_exp_neg_exp_half_le {x : ℝ} (hx : 0 ≤ x) : Real.exp (-Real.exp (x / 2)) ≤ Real.exp (-(x ^ 2 / 8)) := by
      refine Real.exp_le_exp.mpr ?_
      have := Real.quadratic_le_exp_of_nonneg (show 0 ≤ x / 2 by linarith)
      linarith
    have laplaceBase_gaussian_shift_le (x : ℝ) : Real.exp (-(x / 2 - a) ^ 2 / (4 * b)) ≤
          Real.exp (a ^ 2 / (4 * b)) * Real.exp (-(x ^ 2 / (32 * b))) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h : a ^ 2 / (4 * b) + -(x ^ 2 / (32 * b)) - (-(x / 2 - a) ^ 2 / (4 * b)) =
          (x - 4 * a) ^ 2 / (32 * b) := by
        field_simp
        ring
      have h2 : 0 ≤ (x - 4 * a) ^ 2 / (32 * b) := by positivity
      linarith
    have hb32 : 0 < 1 / (32 * b) := by positivity
    set c : ℝ := min (1 / (32 * b)) (1 / 8)
    have hc0 : 0 < c := lt_min hb32 (by norm_num)
    have hc1 : c ≤ 1 / (32 * b) := min_le_left _ _
    have hc2 : c ≤ 1 / 8 := min_le_right _ _
    refine ⟨Real.exp (a ^ 2 / (4 * b)) + 1 + Real.exp (c * (2 * a) ^ 2), c, hc0,
      fun L x hx hL h => ?_⟩
    set E : ℝ := Real.exp (-c * x ^ 2) with hE
    have hE0 : 0 < E := Real.exp_pos _
    by_cases hax : a < x / 2
    · have h1 := h hax
      have h2 := laplaceBase_gaussian_shift_le x
      have := laplaceBase_exp_neg_exp_half_le hx
      have h4 : Real.exp (-(x ^ 2 / (32 * b))) ≤ E := by
        refine Real.exp_le_exp.mpr ?_
        have hmul := mul_le_mul_of_nonneg_right hc1 (sq_nonneg x)
        have e : 1 / (32 * b) * x ^ 2 = x ^ 2 / (32 * b) := by ring
        linarith
      have : Real.exp (-(x ^ 2 / 8)) ≤ E := by
        refine Real.exp_le_exp.mpr ?_
        have hmul := mul_le_mul_of_nonneg_right hc2 (sq_nonneg x)
        have : 1 / 8 * x ^ 2 = x ^ 2 / 8 := by ring
        linarith
      have : Real.exp (a ^ 2 / (4 * b)) * Real.exp (-(x ^ 2 / (32 * b))) ≤
          Real.exp (a ^ 2 / (4 * b)) * E :=
        mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
      have : 0 ≤ Real.exp (c * (2 * a) ^ 2) * E := (mul_pos (Real.exp_pos _) hE0).le
      calc L ≤ Real.exp (a ^ 2 / (4 * b)) * E + E := by linarith
        _ ≤ (Real.exp (a ^ 2 / (4 * b)) + 1 + Real.exp (c * (2 * a) ^ 2)) * E := by linarith
    · have hxa : x ≤ 2 * a := by linarith [not_lt.mp hax]
      have h1 : 1 ≤ Real.exp (c * (2 * a) ^ 2) * E := by
        rw [hE, ← Real.exp_add]
        apply Real.one_le_exp
        have := mul_nonneg hc0.le (sub_nonneg.mpr (pow_le_pow_left₀ hx hxa 2))
        linarith
      have : 0 ≤ Real.exp (a ^ 2 / (4 * b)) * E := (mul_pos (Real.exp_pos _) hE0).le
      calc L ≤ 1 := hL
        _ ≤ Real.exp (c * (2 * a) ^ 2) * E := h1
        _ ≤ (Real.exp (a ^ 2 / (4 * b)) + 1 + Real.exp (c * (2 * a) ^ 2)) * E := by linarith
  have laplaceBase_negMoment_le (r V : ℝ) (A : Set ℂ) (hA : MeasurableSet A) (hA0 : gmcReferenceMeasure A ≠ 0) (hAtop : gmcReferenceMeasure A ≠ ⊤) (hV : ∀ x ∈ A, gaussianVariance P (fun ω => Xc ω x r) ≤ V) (a b : ℝ) (hb : b = γ ^ 2 * V / 2) (ha : a = b - Real.log (gmcReferenceMeasure A).toReal) (q : ℝ) (hq : 0 < q) : ∫⁻ ω, (regularizedGMC P Xc γ r ω A) ^ (-q) ∂P ≤
        ENNReal.ofReal (Real.exp (a * q + b * q ^ 2)) := by
    refine (regularizedGMC_inverse_moment_le_variance P X hX Xc hXc γ r q V hq A hA hA0 hAtop
      hV).trans (le_of_eq ?_)
    have hσ := ENNReal.toReal_pos hA0 hAtop
    rw [← ENNReal.ofReal_toReal hAtop, ENNReal.ofReal_rpow_of_pos hσ,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hσ.le _), Real.rpow_def_of_pos hσ, ← Real.exp_add]
    congr 2
    rw [ha, hb]
    ring
  have hDm : MeasurableSet (Metric.ball (0 : ℂ) R) := Metric.isOpen_ball.measurableSet
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = γ ^ 2 * (T + gmcCircleChartRemainder R) / 2 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ,
      a = b - Real.log (gmcReferenceMeasure (Metric.ball (0 : ℂ) R)).toReal := ⟨_, rfl⟩
  have hbpos : 0 < b := by
    rw [hb]
    exact div_pos (mul_pos (pow_pos hγ 2) (add_pos_of_nonneg_of_pos hT (laplaceBase_chartRemainder_pos hR))) two_pos
  obtain ⟨A, c, hc, hcore⟩ := laplaceBase_real_core a b hbpos
  refine ⟨A, c, hc, fun r hr0 hrT x hx0 => ?_⟩
  have hvar : ∀ y ∈ Metric.ball (0 : ℂ) R,
      gaussianVariance P (fun ω => Xc ω y r) ≤ T + gmcCircleChartRemainder R := fun y hy =>
    gmcCircle_variance_le_coarse_chart P X hX Xc hXc R r T hR.le hr0 hrT y
      (mem_ball_zero_iff.mp hy).le
  have hmom : ∀ q : ℝ, 0 < q →
      ∫⁻ ω, (regularizedGMC P Xc γ r ω (Metric.ball 0 R)) ^ (-q) ∂P ≤
        ENNReal.ofReal (Real.exp (a * q + b * q ^ 2)) := fun q hq =>
    laplaceBase_negMoment_le r _ _ hDm ((laplaceBase_ball_pos).ne') (laplaceBase_ball_ne_top R) hvar a b hb ha q hq
  exact hcore _ x hx0 (cutoffLaplace_le_one P X hX Xc γ r _ x) fun hax =>
    laplaceBase_cutoffLaplace_le_of_negMoment r _ hDm a b hbpos hmom x hax

end DOZZ.Proofs
