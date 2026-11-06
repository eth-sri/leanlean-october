/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitReferenceAvoidance

/-!
# Recentered reference-kernel avoidance

The deterministic-time reference kernel, restricted to staying above a positive level and
recentered at that level, is the same conditioned entrance kernel started from the reduced state.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Strict avoidance in the rational future coordinates. -/
def brownianRationalFutureAbove (c : ℝ) : Set (ℚ → ℝ) :=
  ⋂ r : ℚ, if _hr : 0 < (r : ℝ) then {y | c < y r} else Set.univ

theorem measurableSet_brownianRationalFutureAbove c :
    MeasurableSet (brownianRationalFutureAbove c) := by
  unfold brownianRationalFutureAbove
  apply MeasurableSet.iInter
  intro r
  by_cases hr : 0 < (r : ℝ)
  · simp only [dite_eq_left hr]
    exact measurableSet_lt measurable_const (measurable_pi_apply r)
  · simp [hr]

private noncomputable def brownianReferenceRationalEvalMap (x : ℝ) :
    BrownianPath → (ℚ → ℝ) := fun q =>
      brownianUpperConditionedPositiveRationalEvals x q



/-- The deterministic-time Brownian reference kernel's future, restricted to avoiding `c` and
recentered by `c`, has the reference law started from `x-c`. -/
theorem brownianUpperConditionedReferenceFutureKernel_avoidance_shift_lintegral
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (ν c x : ℝ) (hν : 0 < ν) (hc : 0 < c) (hcx : c < x)
    (G : (ℚ → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ y, (brownianRationalFutureAbove c).indicator
        (fun z => G (fun r => z r - c)) y ∂
          brownianUpperConditionedReferenceFutureKernel B ν hν x) =
      ENNReal.ofReal (lastExitAvoidanceFactor ν c x) *
        ∫⁻ y, G y ∂brownianUpperConditionedReferenceFutureKernel B ν hν (x - c) := by
  classical
  have brownianReferenceRationalAvoidance_iff_below q : brownianReferenceRationalEvalMap x q ∈ brownianRationalFutureAbove c ↔ q ∈ brownianPositiveRationalBelow (x - c) := by
    constructor
    · intro h
      simp only [brownianPositiveRationalBelow, Set.mem_iInter]
      simp only [brownianRationalFutureAbove, Set.mem_iInter] at h
      intro r
      by_cases hr : 0 < (r : ℝ)
      · have hh := h r
        simp only [hr, dite_eq_left, Set.mem_ofPred_eq] at hh ⊢
        rw [(show brownianReferenceRationalEvalMap x q r = x - q ⟨(r : ℝ), hr.le⟩ by simp [brownianReferenceRationalEvalMap, brownianUpperConditionedPositiveRationalEvals, brownianUpperConditionedPositivePath, max_eq_left hr.le])] at hh
        linarith
      · simp [hr]
    · intro h
      simp only [brownianRationalFutureAbove, Set.mem_iInter]
      simp only [brownianPositiveRationalBelow, Set.mem_iInter] at h
      intro r
      by_cases hr : 0 < (r : ℝ)
      · have hh := h r
        simp only [hr, dite_eq_left, Set.mem_ofPred_eq] at hh ⊢
        rw [(show brownianReferenceRationalEvalMap x q r = x - q ⟨(r : ℝ), hr.le⟩ by simp [brownianReferenceRationalEvalMap, brownianUpperConditionedPositiveRationalEvals, brownianUpperConditionedPositivePath, max_eq_left hr.le])]
        linarith
      · simp [hr]
  let E : BrownianPath → (ℚ → ℝ) := fun q =>
    brownianUpperConditionedPositiveRationalEvals x q
  let A := brownianRationalFutureAbove c
  let H : (ℚ → ℝ) → ℝ≥0∞ := fun y => G (fun r => y r - c)
  let R : Set BrownianPath := E ⁻¹' A
  let S := brownianPathStrictlyBelow (x - c)
  have hEval : Measurable E := (measurable_brownianUpperConditionedPositiveRationalEvals.comp ((measurable_const (a := x)).prodMk measurable_id))
  have hA : MeasurableSet A := measurableSet_brownianRationalFutureAbove c
  have hS : MeasurableSet S := measurableSet_brownianPath_below (x - c)
  have hH : Measurable H := by
    apply hG.comp
    apply measurable_pi_iff.mpr
    intro r
    exact (measurable_pi_apply r).sub measurable_const
  have hAvoid : ∀ᵐ q ∂brownianBelowConditionedLaw B ν x, q ∈ R ↔ q ∈ S := by
    filter_upwards [(brownianBelowConditionedLaw_rational_below_ae B hB ν (x - c) x hν (sub_pos.mpr hcx) (by linarith))] with q hq
    change (E q ∈ A ↔ q ∈ brownianPathStrictlyBelow (x - c))
    exact (show E q ∈ A ↔ q ∈ brownianPositiveRationalBelow (x - c) by simpa [E, A, brownianReferenceRationalEvalMap] using brownianReferenceRationalAvoidance_iff_below q).trans hq
  have hMapX := brownianUpperConditionedReferenceFutureKernel_apply_conditioned
    B ν x hν (by linarith : 0 < x)
  have hEvalXc : Measurable (fun q =>
      brownianUpperConditionedPositiveRationalEvals (x - c) q) :=
    measurable_brownianUpperConditionedPositiveRationalEvals.comp
      ((measurable_const (a := x - c)).prodMk measurable_id)
  let F : BrownianPath → ℝ≥0∞ := fun q => G (brownianPathRationalEvals q)
  calc
    (∫⁻ y, A.indicator H y ∂
        brownianUpperConditionedReferenceFutureKernel B ν hν x) =
      ∫⁻ q, A.indicator H (E q) ∂brownianBelowConditionedLaw B ν x := by
        rw [hMapX, lintegral_map (hH.indicator hA) hEval]
    _ = ∫⁻ q, R.indicator (fun q => G (fun r => E q r - c)) q ∂
        brownianBelowConditionedLaw B ν x := by
        apply lintegral_congr
        intro q
        simp [A, H, R, Set.indicator_apply]
    _ = ∫⁻ q, S.indicator (fun q => G (fun r => E q r - c)) q ∂
        brownianBelowConditionedLaw B ν x := by
        apply lintegral_congr_ae
        filter_upwards [hAvoid] with q hq
        simp [Set.indicator_apply, hq]
    _ = ∫⁻ q in S, F (brownianUpperConditionedPositivePath (x - c) q) ∂
          brownianBelowConditionedLaw B ν x := by
        rw [lintegral_indicator hS]
        apply lintegral_congr
        intro q
        congr 1
        funext r
        simp [E,           brownianUpperConditionedPositiveRationalEvals,
          brownianPathRationalEvals, brownianUpperConditionedPositivePath, sub_sub]
       ; ring
    _ = ENNReal.ofReal (lastExitAvoidanceFactor ν c x) *
        ∫⁻ q, F (brownianUpperConditionedPositivePath (x - c) q) ∂
            brownianBelowConditionedLaw B ν (x - c) := by
        exact brownianBelowConditionedLaw_avoidance_shift_integral B hB ν c x
          hν hc hcx _ (by exact hG.comp measurable_brownianPathRationalEvals)
    _ = ENNReal.ofReal (lastExitAvoidanceFactor ν c x) *
      ∫⁻ y, G y ∂brownianUpperConditionedReferenceFutureKernel B ν hν (x - c) := by
        rw [(brownianUpperConditionedReferenceFutureKernel_apply_conditioned B ν (x - c) hν (sub_pos.mpr hcx)), lintegral_map hG hEvalXc]
        congr 1

end DOZZ.Proofs

end
