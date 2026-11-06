/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitConditionalAvoidance
public import DOZZ.Brownian.LastExitStateNoAtoms

/-!
# Full deterministic-time avoidance identity

The shifted-kernel identity is first applied above the barrier. Below the barrier, continuity
makes strict future avoidance impossible. Atomlessness of the deterministic entrance state removes
the endpoint equality case, yielding the full a.e. conditional identity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs



/-- Full a.e. deterministic-time avoidance identity for arbitrary measurable events of the
recentered rational future. The endpoint equality branch is null because the one-time entrance
density is atomless. -/
theorem conditionedPositiveHistory_condExp_rationalFuture_avoidance_shift
    {ν : ℝ} {P : Measure BrownianPath} [IsFiniteMeasure P]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hν : 0 < ν)
    (c : ℝ≥0) (hc : 0 < (c : ℝ))
    C (hC : MeasurableSet C) :
    ∀ᵐ p ∂P,
      P[(conditionedPositiveFutureRationalAvoidance t c).indicator
        (fun p => lastExitShiftedFutureTest (c : ℝ) C
          (conditionedPositiveFutureRationalEvals t p)) |
        conditionedPositiveNaturalFiltration t] p =
        lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt t p) *
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (conditionedPositiveStateAt t p - c)).real C := by
  have conditionedPositiveHistory_condExp_rationalFuture_avoidance_shift_on_below {P : Measure BrownianPath} [IsFiniteMeasure P] (t : ℝ≥0) (c : ℝ≥0) C (hC : MeasurableSet C) : ∀ᵐ p ∂P, conditionedPositiveStateAt t p < (c : ℝ) → P[(conditionedPositiveFutureRationalAvoidance t c).indicator (fun p => lastExitShiftedFutureTest (c : ℝ) C (conditionedPositiveFutureRationalEvals t p)) | conditionedPositiveNaturalFiltration t] p = 0 := by
    classical
    have conditionedPositiveFutureAvoidance_implies_state_ge p (hp : p ∈ conditionedPositiveFutureRationalAvoidance t c) : (c : ℝ) ≤ conditionedPositiveStateAt t p := by
      by_contra hnot
      let F : ℝ → ℝ := fun s => conditionedPositiveFuturePath t p
        ⟨max s 0, le_max_right s 0⟩
      have hF := (conditionedPositiveFuturePath t p).continuous.comp ((continuous_max.comp (continuous_id.prodMk continuous_const)).subtype_mk (fun s => le_max_right s 0))
      have hFzero : F 0 = conditionedPositiveStateAt t p := by
        change -(p (t + ⟨max (0 : ℝ) 0, le_max_right 0 0⟩)) = -(p t)
        rw [(show (⟨max (0 : ℝ) 0, le_max_right 0 0⟩ : ℝ≥0) = 0 by apply Subtype.ext; simp)]
        exact congrArg (fun s : ℝ≥0 => -(p s)) (add_zero t)
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ((isOpen_Iio.preimage hF).mem_nhds (show (0 : ℝ) ∈ F ⁻¹' Set.Iio (c : ℝ) by rw [Set.mem_preimage, hFzero]; exact (lt_of_not_ge hnot)))
      obtain ⟨q, hq0, hqδ⟩ := exists_rat_btwn (show (0 : ℝ) < δ by positivity)
      have hpq := (show ∀ r : ℚ, 0 < (r : ℝ) → (c : ℝ) < conditionedPositiveFutureRationalEvals t p r by intro r hr; simpa [conditionedPositiveFutureAvoidanceCoordinate, hr] using ((Set.mem_iInter.mp hp) r)) q hq0
      rw [(show conditionedPositiveFutureRationalEvals t p q = F (q : ℝ) by simp [F, conditionedPositiveFutureRationalEvals, conditionedPositiveFuturePath, max_eq_left hq0.le])] at hpq
      exact (not_lt_of_ge (le_of_lt (hball (Metric.mem_ball.mpr (by change ‖(q : ℝ) - 0‖ < δ; rw [sub_zero, Real.norm_eq_abs, abs_of_pos hq0]; exact hqδ))))) hpq
    let eval := conditionedPositiveFutureRationalEvals t
    let shift := lastExitRationalShift (c : ℝ)
    let test := lastExitShiftedFutureTest (c : ℝ) C
    let shiftedEval : BrownianPath → (ℚ → ℝ) := fun p => shift (eval p)
    let avoid : Set BrownianPath := conditionedPositiveFutureRationalAvoidance t c
    let E : Set BrownianPath := {p | (c : ℝ) ≤ conditionedPositiveStateAt t p}
    let f : BrownianPath → ℝ := fun p => avoid.indicator
      (fun p => test (eval p)) p
    let g : BrownianPath → ℝ := E.indicator (fun _ => 1)
    have hshift : Measurable shift := by
      apply measurable_pi_iff.mpr
      intro r
      exact (measurable_pi_apply r).sub measurable_const
    have heval := measurable_conditionedPositiveFutureRationalEvals t
    have havoid : MeasurableSet avoid := by
      change MeasurableSet (⋂ q : ℚ,
        conditionedPositiveFutureAvoidanceCoordinate t c q)
      apply MeasurableSet.iInter
      intro q
      by_cases hq : 0 < (q : ℝ)
      · simp only [conditionedPositiveFutureAvoidanceCoordinate, hq]
        exact measurableSet_lt measurable_const
          ((measurable_pi_apply q).comp heval)
      · simp [conditionedPositiveFutureAvoidanceCoordinate, hq]
    have hf_eq : f = (avoid ∩ shiftedEval ⁻¹' C).indicator (fun _ => (1 : ℝ)) := by
      funext p
      by_cases hp : p ∈ avoid
      · by_cases hq : shiftedEval p ∈ C
        · simp [f, test, lastExitShiftedFutureTest, avoid, hp, hq,
            shiftedEval, shift, eval]
        · simp [f, test, lastExitShiftedFutureTest, avoid, hp, hq,
            shiftedEval, shift, eval]
      · simp [f, avoid, hp]
    have hgInt : Integrable g P := by
      exact (integrable_const (1 : ℝ)).indicator (measurableSet_le measurable_const ((measurable_conditionedPositiveStateAt t).comp measurable_id))
    have hstateFil : Measurable[conditionedPositiveNaturalFiltration t]
        (conditionedPositiveStateAt t) := by
      apply Measurable.of_comap_le
      change MeasurableSpace.comap (conditionedPositiveProcessValue t) inferInstance ≤
        conditionedPositiveNaturalFiltration t
      exact le_iSup_of_le t (le_iSup_of_le le_rfl le_rfl)
    have hfg : f ≤ᵐ[P] g := by
      apply Filter.Eventually.of_forall
      intro p
      by_cases hp : p ∈ avoid
      · have hpE : p ∈ E := by
          exact conditionedPositiveFutureAvoidance_implies_state_ge p hp
        change avoid.indicator (fun q => test (eval q)) p ≤
          E.indicator (fun _ => (1 : ℝ)) p
        by_cases hq : shiftedEval p ∈ C
        · have htest : test (eval p) = 1 := by
            simp [test, lastExitShiftedFutureTest, shiftedEval, shift, eval, hq]
          rw [Set.indicator_of_mem hp, Set.indicator_of_mem hpE, htest]
        · have htest : test (eval p) = 0 := by
            simp [test, lastExitShiftedFutureTest, shiftedEval, shift, eval, hq]
          rw [Set.indicator_of_mem hp, Set.indicator_of_mem hpE, htest]
          norm_num
      · by_cases hpE : p ∈ E
        · simp [f, g, avoid, E, hp, hpE]
        · simp [f, g, avoid, E, hp, hpE]
    have hfilLe : conditionedPositiveNaturalFiltration t ≤ ContinuousMap.measurableSpace := by
      refine iSup_le fun s => iSup_le fun _ => ?_
      exact (measurable_conditionedPositiveProcessValue s).comap_le
    have hfNonneg : 0 ≤ᵐ[P] f := by
      apply Filter.Eventually.of_forall
      intro p
      by_cases hp : p ∈ avoid
      · have htest0 : 0 ≤ test (eval p) := by
          by_cases hq : shiftedEval p ∈ C
          · simp [test, lastExitShiftedFutureTest, shiftedEval, shift, eval, hq]
          · simp [test, lastExitShiftedFutureTest, shiftedEval, shift, eval, hq]
        change 0 ≤ avoid.indicator (fun q => test (eval q)) p
        rw [Set.indicator_of_mem hp]
        exact htest0
      · change 0 ≤ avoid.indicator (fun q => test (eval q)) p
        simp [Set.indicator_of_notMem hp]
    filter_upwards [((condExp_mono (m := conditionedPositiveNaturalFiltration t) (by rw [hf_eq]; exact (integrable_const (1 : ℝ)).indicator (havoid.inter (hC.preimage (hshift.comp heval)))) hgInt hfg).trans_eq (by filter_upwards [] with p; exact congrFun (condExp_of_stronglyMeasurable (μ := P) hfilLe (by exact (measurable_const.indicator (measurableSet_le measurable_const hstateFil)).stronglyMeasurable) hgInt) p)), (condExp_nonneg (m := conditionedPositiveNaturalFiltration t) hfNonneg)] with p hle hnonneg
    intro hbelow
    exact le_antisymm (by simpa [(show g p = 0 by simp [g, E, (show p ∉ E by simp [E, not_le.mpr hbelow])])] using hle) hnonneg
  filter_upwards [(ae_conditionedPositiveStateAt_ne hP t ht (c : ℝ)), (conditionedPositiveHistory_condExp_rationalFuture_avoidance_shift_on_above hP B hB t ht hν c hc C hC), (conditionedPositiveHistory_condExp_rationalFuture_avoidance_shift_on_below (P := P) t c C hC)] with p hpneq hpabove hpbelow
  by_cases hcx : (c : ℝ) < conditionedPositiveStateAt t p
  · exact hpabove hcx
  · have hle : conditionedPositiveStateAt t p ≤ (c : ℝ) := le_of_not_gt hcx
    rw [hpbelow (lt_of_le_of_ne hle hpneq)]
    simp [lastExitAvoidanceFactor, hcx]

/-- The conditional probability of avoiding the level after a deterministic time is exactly the
Doob harmonic ratio from the current state. This is the empty-test case of the full rational-future
identity. -/
theorem conditionedPositiveHistory_condExp_rationalFuture_avoidance_probability
    {ν : ℝ} {P : Measure BrownianPath} [IsFiniteMeasure P]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hν : 0 < ν)
    (c : ℝ≥0) (hc : 0 < (c : ℝ)) :
    ∀ᵐ p ∂P,
      P[(conditionedPositiveFutureRationalAvoidance t c).indicator
        (fun _ => (1 : ℝ)) | conditionedPositiveNaturalFiltration t] p =
        lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt t p) := by
  have hmass x :
      lastExitAvoidanceFactor ν (c : ℝ) x *
        (brownianUpperConditionedReferenceFutureKernel B ν hν (x - c)).real
          Set.univ = lastExitAvoidanceFactor ν (c : ℝ) x := by
    by_cases hcx : (c : ℝ) < x
    · have hx : 0 < x - (c : ℝ) := sub_pos.mpr hcx
      have : IsProbabilityMeasure
          (brownianBelowConditionedLaw B ν (x - (c : ℝ))) :=
        isProbabilityMeasure_brownianBelowConditionedLaw B hB ν (x - (c : ℝ)) hν hx
      have : IsProbabilityMeasure
          (brownianUpperConditionedReferenceFutureKernel B ν hν (x - (c : ℝ))) := by
        rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned
          B ν (x - (c : ℝ)) hν hx]
        infer_instance
      rw [(show (brownianUpperConditionedReferenceFutureKernel B ν hν (x - (c : ℝ))).real Set.univ = 1 by rw [measureReal_def]; simp), mul_one]
    · simp [lastExitAvoidanceFactor, hcx]
  filter_upwards [(conditionedPositiveHistory_condExp_rationalFuture_avoidance_shift hP B hB t ht hν c hc Set.univ MeasurableSet.univ)] with p hp
  simpa [lastExitShiftedFutureTest, hmass] using hp

end DOZZ.Proofs

end
