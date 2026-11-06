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

private theorem lastExitAvoidanceFactor_nonneg_le_one
    {ν c y : ℝ} (hν : 0 < ν) (hc : 0 < c) :
    0 ≤ lastExitAvoidanceFactor ν c y ∧ lastExitAvoidanceFactor ν c y ≤ 1 := by
  by_cases hcy : c < y
  · have hy := lt_trans hc hcy
    have hyc := sub_pos.mpr hcy
    have hnumExp : Real.exp (-2 * ν * (y - c)) < 1 := by
      simp_all
    have hdenExp : Real.exp (-2 * ν * y) < 1 := by
      simp_all
    have hnum : 0 < 1 - Real.exp (-2 * ν * (y - c)) := by linarith
    have hden : 0 < 1 - Real.exp (-2 * ν * y) := by linarith
    have harg : -2 * ν * y ≤ -2 * ν * (y - c) := by
      nlinarith
    have hratio : 1 - Real.exp (-2 * ν * (y - c)) ≤
        1 - Real.exp (-2 * ν * y) := by
      bound
    have hfactor : lastExitAvoidanceFactor ν c y =
        (1 - Real.exp (-2 * ν * (y - c))) /
          (1 - Real.exp (-2 * ν * y)) := by
      simp [lastExitAvoidanceFactor, conditionedH, hν.ne', hcy]
    rw [hfactor]
    bound
  · simp [lastExitAvoidanceFactor, hcy]

private theorem measurable_lastExitAvoidanceFactor
    (ν c : ℝ) : Measurable (lastExitAvoidanceFactor ν c) := by
  unfold lastExitAvoidanceFactor
  apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
  · have hH : Measurable (fun y : ℝ => conditionedH ν y) := by
      by_cases hzero : ν = 0
      · simp [conditionedH, hzero]
        fun_prop
      · simp [conditionedH, hzero]
        fun_prop
    exact (hH.comp (measurable_id.sub measurable_const)).div hH
  simp

/-- The expected avoidance probability at time `t` converges to one for a positive-drift
conditioned entrance path. -/
theorem tendsto_integral_lastExitAvoidanceFactor_atTop
    {ν : ℝ} {P : Measure BrownianPath}
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hν : 0 < ν) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun t : ℝ≥0 =>
      ∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P) atTop (𝓝 1) := by
  let : IsProbabilityMeasure P := hP.2.1
  have hstate := conditionedPositiveStateAt_measureReal_Iic_tendsto_zero_atTop
    hP hν
  have hmeasFactor :=
    measurable_lastExitAvoidanceFactor ν c
  have hfactorBound (x : ℝ) :
      0 ≤ lastExitAvoidanceFactor ν c x ∧ lastExitAvoidanceFactor ν c x ≤ 1 :=
    lastExitAvoidanceFactor_nonneg_le_one hν hc
  have hX (t : ℝ≥0) : Measurable (fun p : BrownianPath => -(p t)) :=
    (ContinuousMap.measurable_eval t).neg
  have hInt (t : ℝ≥0) : Integrable
      (fun p : BrownianPath => lastExitAvoidanceFactor ν c (-(p t))) P := by
    apply Integrable.mono' (integrable_const 1)
      ((hmeasFactor.comp (hX t)).aestronglyMeasurable)
    filter_upwards [] with p
    change ‖lastExitAvoidanceFactor ν c (-(p t))‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (hfactorBound (-(p t))).1]
    simp_all
  have hIntegralBound (t : ℝ≥0) :
      0 ≤ (∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P) ∧
      (∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P) ≤ 1 := by
    constructor
    · exact integral_nonneg (fun p => (hfactorBound (-(p t))).1)
    · calc
        _ ≤ ∫ _ : BrownianPath, 1 ∂P :=
          integral_mono (hInt t) (integrable_const 1)
            (fun p => (hfactorBound (-(p t))).2)
        _ = 1 := by simp
  have hsmall (M : ℝ) (hM : 0 < M) :
      Tendsto (fun t : ℝ≥0 => P.real {p | -(p t) ≤ M}) atTop (𝓝 0) :=
    conditionedPositiveStateAt_measureReal_Iic_tendsto_zero_atTop hP hν M hM
  have hLower : ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ≥0 in atTop,
      1 - ε ≤ ∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P := by
    intro ε hε
    let δ := ε / 2
    have hδ : 0 < δ := by positivity
    have hlarge : ∀ᶠ y : ℝ in atTop,
        1 - δ < lastExitAvoidanceFactor ν c y :=
      (lastExitAvoidanceFactor_tendsto_one_atTop (ν := ν) (c := c) hν).eventually (Ioi_mem_nhds (by linarith))
    obtain ⟨M₀, hM₀⟩ := (eventually_atTop.1 hlarge)
    let M := max M₀ (max c 1)
    have hM : 0 < M := by positivity
    filter_upwards [(hsmall M hM).eventually (Iio_mem_nhds hδ)] with t ht
    have hA : MeasurableSet {p : BrownianPath | -(p t) ≤ M} :=
      measurableSet_le (hX t) measurable_const
    let f : BrownianPath → ℝ := fun p => 1 - lastExitAvoidanceFactor ν c (-(p t))
    let g : BrownianPath → ℝ := fun p =>
      ({p : BrownianPath | -(p t) ≤ M}).indicator (fun _ => 1) p + δ
    have hf : Integrable f P := by
      have hconst : Integrable (fun _ : BrownianPath => (1 : ℝ)) P := integrable_const 1
      exact (hconst.sub (hInt t)).congr (Filter.Eventually.of_forall fun p => by rfl)
    have hg : Integrable g P := by fun_prop
    have hfg : f ≤ g := by
      intro p
      by_cases hp : -(p t) ≤ M
      · have hnonneg := (hfactorBound (-(p t))).1
        simp [f, g, hp]
        linarith
      · have hgt := lt_of_not_ge hp
        have hlarg := hM₀ (-(p t)) (le_trans (le_max_left ..) hgt.le)
        have hlt : 1 - lastExitAvoidanceFactor ν c (-(p t)) < δ := by linarith
        simp [f, g, hp]
        linarith
    have hbound : ∫ p, f p ∂P ≤ P.real {p | -(p t) ≤ M} + δ := by
      calc
        _ ≤ ∫ p, g p ∂P := integral_mono hf hg hfg
        _ = (∫ p, ({p : BrownianPath | -(p t) ≤ M}.indicator
            (fun _ => 1)) p ∂P) + ∫ p, δ ∂P := by
              rw [integral_add ((integrable_const 1).indicator hA)
                (integrable_const δ)]
        _ = P.real {p | -(p t) ≤ M} + δ := by
          have hInd :
              (∫ p, ({p : BrownianPath | -(p t) ≤ M}.indicator
                (fun _ => 1)) p ∂P) = P.real {p | -(p t) ≤ M} := by
            calc
              _ = ∫ p, ({p : BrownianPath | -(p t) ≤ M}.indicator
                  1) p ∂P := by
                    congr 1
              _ = P.real {p | -(p t) ≤ M} := integral_indicator_one hA
          rw [hInd]
          simp
    have htotal : ∫ p, f p ∂P =
        1 - ∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P := by
      calc
        _ = ∫ p, (1 - lastExitAvoidanceFactor ν c (-(p t))) ∂P := rfl
        _ = (∫ _ : BrownianPath, 1 ∂P) -
            ∫ p, lastExitAvoidanceFactor ν c _ ∂P :=
          integral_sub (integrable_const 1) (hInt t)
        _ = _ := by simp
    dsimp [δ] at hbound ht hδ
    nlinarith
  have htop : ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ≥0 in atTop,
      (∫ p, lastExitAvoidanceFactor ν c (-(p t)) ∂P) < 1 + ε := by
    intro ε hε
    exact Filter.Eventually.of_forall fun t => by
      linarith [(hIntegralBound t).2]
  apply tendsto_order.2
  constructor
  · intro a ha
    have hε : 0 < (1 - a) / 2 := by linarith
    filter_upwards [hLower _ hε] with t ht
    nlinarith
  · intro a ha
    have hε : 0 < a - 1 := by linarith
    filter_upwards [htop _ hε] with t ht
    linarith

end DOZZ.Proofs

end
