/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitEntranceTail
public import DOZZ.Brownian.LastExitAvoidanceLimit

/-!
# Mean convergence of the deterministic-time avoidance factor

The entrance state escapes every fixed lower interval, and the avoidance factor tends to one as
its state grows. This file combines those two facts at the level of the conditioned path law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal Topology

namespace DOZZ.Proofs


private theorem measurable_lastExitAvoidanceFactor
    ν c : Measurable (lastExitAvoidanceFactor ν c) := by
  unfold lastExitAvoidanceFactor
  apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
  · have hH : Measurable (fun y => conditionedH ν y) := by
      by_cases hzero : ν = 0
      · simp [conditionedH, hzero]
        fun_prop
      · simp [conditionedH, hzero]
        fun_prop
    exact (hH.comp (measurable_id.sub measurable_const)).div hH
  · exact measurable_const

/-- The expected avoidance probability at time `t` converges to one for a positive-drift
conditioned entrance path. -/
theorem tendsto_integral_lastExitAvoidanceFactor_atTop
    {ν} {P : Measure BrownianPath}
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hν : 0 < ν) c (hc : 0 < c) :
    Tendsto (fun t : ℝ≥0 =>
      ∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P) atTop (𝓝 1) := by
  have lastExitAvoidanceFactor_nonneg_le_one {y} : 0 ≤ lastExitAvoidanceFactor ν c y ∧ lastExitAvoidanceFactor ν c y ≤ 1 := by
    by_cases hcy : c < y
    · have hy : 0 < y := lt_trans hc hcy
      have := sub_pos.mpr hcy
      have : Real.exp (-2 * ν * (y - c)) < 1 := by
        apply Real.exp_lt_one_iff.mpr
        nlinarith
      have : Real.exp (-2 * ν * y) < 1 := by
        apply Real.exp_lt_one_iff.mpr
        nlinarith
      have hden : 0 < 1 - Real.exp (-2 * ν * y) := by linarith
      have hratio : 1 - Real.exp (-2 * ν * (y - c)) ≤
          1 - Real.exp (-2 * ν * y) := by
        have := Real.exp_le_exp.mpr (show -2 * ν * y ≤ -2 * ν * (y - c) by nlinarith)
        linarith
      rw [(show lastExitAvoidanceFactor ν c y = (1 - Real.exp (-2 * ν * (y - c))) / (1 - Real.exp (-2 * ν * y)) by simp [lastExitAvoidanceFactor, conditionedH, hν.ne', hcy])]
      exact ⟨(div_nonneg (show 0 < 1 - Real.exp (-2 * ν * (y - c)) by linarith).le hden.le), (div_le_one hden).2 hratio⟩
    · simp [lastExitAvoidanceFactor, hcy]
  let : IsProbabilityMeasure P := hP.2.1
  have := conditionedPositiveStateAt_measureReal_Iic_tendsto_zero_atTop
    hP hν
  have hfactorBound x :
      0 ≤ lastExitAvoidanceFactor ν c x ∧ lastExitAvoidanceFactor ν c x ≤ 1 :=
    lastExitAvoidanceFactor_nonneg_le_one
  have hX (t : ℝ≥0) : Measurable (fun p : BrownianPath => -(p t)) :=
    (ContinuousMap.measurable_eval t).neg
  have hInt (t : ℝ≥0) : Integrable
      (fun p : BrownianPath => lastExitAvoidanceFactor ν c (-(p t))) P := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (((measurable_lastExitAvoidanceFactor ν c).comp (hX t)).aestronglyMeasurable)
    filter_upwards [] with p
    change ‖lastExitAvoidanceFactor ν c (-(p t))‖ ≤ (1 : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (hfactorBound (-(p t))).1]
    simpa using (hfactorBound (-(p t))).2
  have hIntegralBound (t : ℝ≥0) :
      0 ≤ (∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P) ∧
      (∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P) ≤ 1 := by
    constructor
    · exact integral_nonneg (fun p => (hfactorBound (-(p t))).1)
    · calc
        _ ≤ ∫ _ : BrownianPath, (1 : ℝ) ∂P :=
          integral_mono (hInt t) (integrable_const 1)
            (fun p => (hfactorBound (-(p t))).2)
        _ = 1 := by simp
  have hLower : ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ≥0 in atTop,
      1 - ε ≤ ∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P := by
    intro ε hε
    let δ : ℝ := ε / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    obtain ⟨M₀, hM₀⟩ := (eventually_atTop.1 ((lastExitAvoidanceFactor_tendsto_one_atTop (ν := ν) (c := c) hν).eventually (Ioi_mem_nhds (by linarith)) : ∀ᶠ y : ℝ in atTop, 1 - δ < lastExitAvoidanceFactor ν c y))
    let M : ℝ := max M₀ (max c 1)
    filter_upwards [((fun (M : ℝ) (hM : 0 < M) => conditionedPositiveStateAt_measureReal_Iic_tendsto_zero_atTop hP hν M hM) M (by dsimp [M]; positivity)).eventually (Iio_mem_nhds hδ)] with t ht
    have hA : MeasurableSet {p : BrownianPath | -(p t) ≤ M} :=
      measurableSet_le (hX t) measurable_const
    let f : BrownianPath → ℝ := fun p => 1 - lastExitAvoidanceFactor ν c (-(p t))
    let g : BrownianPath → ℝ := fun p =>
      ({p : BrownianPath | -(p t) ≤ M}).indicator (fun _ => (1 : ℝ)) p + δ
    have hfg : f ≤ g := by
      intro p
      by_cases hp : -(p t) ≤ M
      · have hnonneg := (hfactorBound (-(p t))).1
        simp [f, g, hp]
        linarith
      · have hgt : M < -(p t) := lt_of_not_ge hp
        have := hM₀ (-(p t)) (le_trans (le_max_left _ _) hgt.le)
        have : 1 - lastExitAvoidanceFactor ν c (-(p t)) < δ := by linarith
        simp [f, g, hp]
        linarith
    have hbound : ∫ p, f p ∂P ≤ P.real {p | -(p t) ≤ M} + δ := by
      calc
        _ ≤ ∫ p, g p ∂P := integral_mono (by exact ((integrable_const 1).sub (hInt t)).congr (Filter.Eventually.of_forall fun p => by simp [f])) (by exact ((integrable_const (1 : ℝ)).indicator hA).add (integrable_const δ)) hfg
        _ = (∫ p, ({p : BrownianPath | -(p t) ≤ M}.indicator
            (fun _ => (1 : ℝ))) p ∂P) + ∫ p, (δ : ℝ) ∂P := by
              rw [integral_add ((integrable_const (1 : ℝ)).indicator hA)
                (integrable_const δ)]
        _ = P.real {p | -(p t) ≤ M} + δ := by
          have hInd :
              (∫ p, ({p : BrownianPath | -(p t) ≤ M}.indicator
                (fun _ => (1 : ℝ))) p ∂P) = P.real {p | -(p t) ≤ M} := by
            calc
              _ = ∫ p, ({p : BrownianPath | -(p t) ≤ M}.indicator
                  (1 : BrownianPath → ℝ)) p ∂P := by
                    congr 1
              _ = P.real {p | -(p t) ≤ M} := integral_indicator_one hA
          rw [hInd]
          simp
    have htotal : ∫ p, f p ∂P =
        1 - ∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P := by
      calc
        _ = ∫ p, (1 - lastExitAvoidanceFactor ν c (-(p t))) ∂P := rfl
        _ = (∫ _ : BrownianPath, (1 : ℝ) ∂P) -
            ∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P :=
          integral_sub (integrable_const 1) (hInt t)
        _ = _ := by simp
    rw [htotal] at hbound
    dsimp [δ] at hbound ht hδ
    nlinarith [ht, hbound]
  have htop : ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ≥0 in atTop,
      (∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P) < 1 + ε := by
    intro ε hε
    exact Filter.Eventually.of_forall fun t => by
      linarith [(hIntegralBound t).2]
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hLower ((1 - a) / 2) (by linarith)] with t ht
    nlinarith [ht]
  · intro a ha
    filter_upwards [htop (a - 1) (by linarith)] with t ht
    linarith

end DOZZ.Proofs

end
