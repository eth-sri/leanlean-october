/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitReferenceKernel
public import DOZZ.Brownian.Williams.MaximumGeometry

/-!
# No tangencies for the deterministic-time Brownian reference future

The atomless drifted-Brownian maximum law removes the only discrepancy between strict rational
survival and avoidance at every real future time. This is the boundary input needed to turn the
late-time rational survival limit into a last-exit bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- A positive rational future stays strictly positive and approaches zero somewhere. For a
continuous positive path this records a real-time touch of the boundary. -/
def brownianPositiveRationalTouchZero : Set (ℚ → ℝ) :=
  {y | (∀ r : ℚ, 0 < (r : ℝ) → 0 < y r) ∧
    ∀ n : ℕ, ∃ r : ℚ, 0 < (r : ℝ) ∧ y r < 1 / ((n : ℝ) + 1)}

theorem measurableSet_brownianPositiveRationalTouchZero :
    MeasurableSet brownianPositiveRationalTouchZero := by
  change MeasurableSet
    ({y : ℚ → ℝ | (∀ r : ℚ, 0 < (r : ℝ) → 0 < y r) ∧
      ∀ n : ℕ, ∃ r : ℚ, 0 < (r : ℝ) ∧ y r < 1 / ((n : ℝ) + 1)} : Set (ℚ → ℝ))
  have hpos : MeasurableSet
      {y : ℚ → ℝ | ∀ r : ℚ, 0 < (r : ℝ) → 0 < y r} := by
    rw [(show {y : ℚ → ℝ | ∀ r : ℚ, 0 < (r : ℝ) → 0 < y r} = ⋂ r : ℚ, if hr : 0 < (r : ℝ) then {y : ℚ → ℝ | 0 < y r} else Set.univ by ext y; simp)]
    exact MeasurableSet.iInter fun r => by
      by_cases hr : 0 < (r : ℝ)
      · simp only [hr, dite_true]
        exact measurableSet_lt measurable_const (measurable_pi_apply r)
      · simp [hr]
  have hnearEq (n : ℕ) : {y : ℚ → ℝ | ∃ r : ℚ,
      0 < (r : ℝ) ∧ y r < 1 / ((n : ℝ) + 1)} =
      ⋃ r : ℚ, if hr : 0 < (r : ℝ) then
        {y : ℚ → ℝ | y r < 1 / ((n : ℝ) + 1)} else ∅ := by
    ext y
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨r, hr, hy⟩
      exact ⟨r, by simpa only [hr, dite_true, mem_ofPred_eq] using
        (show y r < 1 / ((n : ℝ) + 1) from hy)⟩
    · rintro ⟨r, hr⟩
      by_cases hq : 0 < (r : ℝ)
      · simp only [hq, dite_true, mem_ofPred_eq] at hr
        exact ⟨r, hq, by simpa only [one_div] using hr⟩
      · simp [hq] at hr
  have hnear : MeasurableSet
      {y : ℚ → ℝ | ∀ n : ℕ, ∃ r : ℚ,
        0 < (r : ℝ) ∧ y r < 1 / ((n : ℝ) + 1)} := by
    rw [show {y : ℚ → ℝ | ∀ n : ℕ, ∃ r : ℚ,
        0 < (r : ℝ) ∧ y r < 1 / ((n : ℝ) + 1)} =
        ⋂ n : ℕ, {y : ℚ → ℝ | ∃ r : ℚ,
          0 < (r : ℝ) ∧ y r < 1 / ((n : ℝ) + 1)} by
          ext y
          simp]
    exact MeasurableSet.iInter fun n => by
      rw [hnearEq n]
      exact MeasurableSet.iUnion fun r => by
        by_cases hr : 0 < (r : ℝ)
        · simp only [hr, dite_true]
          exact measurableSet_lt (measurable_pi_apply r) measurable_const
        · simp [hr]
  change MeasurableSet
    ({y : ℚ → ℝ | ∀ r : ℚ, 0 < (r : ℝ) → 0 < y r} ∩
      {y : ℚ → ℝ | ∀ n : ℕ, ∃ r : ℚ,
        0 < (r : ℝ) ∧ y r < 1 / ((n : ℝ) + 1)})
  exact hpos.inter hnear


/-- The Brownian reference future started at any positive state has zero mass on rational
survival accompanied by a real-time boundary touch. -/
theorem brownianUpperConditionedReferenceFutureKernel_measure_touchZero
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (ν a : ℝ) (hν : 0 < ν) (ha : 0 < a) :
    brownianUpperConditionedReferenceFutureKernel B ν hν a
      brownianPositiveRationalTouchZero = 0 := by
  classical
  have rational_strict_upper_bound_path (q : BrownianPath) {a : ℝ} (hq : ∀ r : ℚ, ∀ hr : 0 < (r : ℝ), q ⟨(r : ℝ), hr.le⟩ < a) (t : ℝ≥0) : q t ≤ a := by
    by_contra hnot
    let F : ℝ → ℝ := fun s => q ⟨max s 0, le_max_right s 0⟩
    have hF_eval (s : ℝ) (hs : 0 ≤ s) : F s = q ⟨s, hs⟩ := by
      change q ⟨max s 0, le_max_right s 0⟩ = q ⟨s, hs⟩
      congr 1
      exact Subtype.ext (max_eq_left hs)
    have hopen : IsOpen (F ⁻¹' Set.Ioi a) := isOpen_Ioi.preimage (by apply q.continuous.comp; exact (continuous_max.comp (continuous_id.prodMk continuous_const)).subtype_mk (fun s => le_max_right s 0))
    have htmem : (t : ℝ) ∈ F ⁻¹' Set.Ioi a := by
      rw [Set.mem_preimage, hF_eval (t : ℝ) t.property]
      exact (lt_of_not_ge hnot)
    by_cases htpos : 0 < (t : ℝ)
    · let U : Set ℝ := Set.Ioi 0 ∩ F ⁻¹' Set.Ioi a
      obtain ⟨r, hrU⟩ := Rat.denseRange_cast.exists_mem_open (isOpen_Ioi.inter hopen) ⟨t, htpos, htmem⟩
      have hr : 0 < (r : ℝ) ∧ a < F (r : ℝ) := hrU
      linarith [hr.2, (hq r hr.1), (hF_eval (r : ℝ) hr.1.le)]
    · have ht0 : t = 0 := by
        apply Subtype.ext
        exact le_antisymm (le_of_not_gt htpos) t.property
      subst t
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds htmem)
      obtain ⟨r, hr0, hrδ⟩ := exists_rat_btwn (show (0 : ℝ) < δ by positivity)
      have hrpos := hr0
      have hFr : a < F (r : ℝ) := hball (Metric.mem_ball.mpr (by change ‖(r : ℝ) - 0‖ < δ; rw [sub_zero, Real.norm_eq_abs, abs_of_pos hr0]; exact hrδ))
      linarith [hFr, (hq r hrpos), (hF_eval (r : ℝ) hrpos.le)]
  let D := driftedBrownianPath (-ν)
  let eval := brownianUpperConditionedPositiveRationalEvals a
  let A := eval ⁻¹' brownianPositiveRationalTouchZero
  have hD : Measurable D := continuous_driftedBrownianPath.measurable.comp
    ((measurable_const (a := -ν)).prodMk measurable_id)
  have hEval : Measurable eval :=
    measurable_brownianUpperConditionedPositiveRationalEvals.comp
      (measurable_const.prodMk measurable_id)
  have hA : MeasurableSet A :=
    measurableSet_brownianPositiveRationalTouchZero.preimage hEval
  let _ := noAtoms_brownianMaximumReferenceLaw ν
  have hmaxzero : B {p | driftedBrownianMaximum ν p = a} = 0 := by
    have hsingle := congrArg (fun m : Measure ℝ => m {a}) (brownianPath_globalMaximum_map B hB ν hν)
    rw [Measure.map_apply_of_aemeasurable (aemeasurable_driftedBrownianMaximum B hB ν hν) (measurableSet_singleton a)] at hsingle
    simpa only [Set.preimage, mem_singleton_iff, eq_comm, measure_singleton] using hsingle
  have hsubset : D ⁻¹' A ⊆ {p | driftedBrownianMaximum ν p = a} := by
    intro p hp
    have htouch := hp
    have hrat : ∀ r : ℚ, ∀ hr : 0 < (r : ℝ),
        D p ⟨(r : ℝ), hr.le⟩ < a := by
      intro r hr
      have h := htouch.1 r hr
      change 0 < a - D p ⟨max (r : ℝ) 0, le_max_right _ _⟩ at h
      rw [(show (⟨max (r : ℝ) 0, le_max_right _ _⟩ : ℝ≥0) = ⟨(r : ℝ), hr.le⟩ by apply Subtype.ext; exact max_eq_left hr.le)] at h
      linarith
    have hweak := rational_strict_upper_bound_path (D p) hrat
    have hsup : driftedBrownianMaximum ν p =
        sSup (Set.range (fun t : ℝ≥0 => D p t)) := by
      unfold driftedBrownianMaximum
      congr 1
      ext z
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨t, by simp [D, driftedBrownianPath, neg_mul, sub_eq_add_neg]⟩
      · rintro ⟨t, ht⟩
        exact ⟨t, by simpa [D, driftedBrownianPath, neg_mul, sub_eq_add_neg] using ht⟩
    have hle : driftedBrownianMaximum ν p ≤ a := by
      rw [hsup]
      exact csSup_le (Set.range_nonempty _) (by
        rintro z ⟨t, rfl⟩
        exact hweak t)
    have hge : a ≤ driftedBrownianMaximum ν p := by
      by_contra hnot
      have : sSup (Set.range (fun t : ℝ≥0 => D p t)) < a := by
        rw [← hsup]
        exact lt_of_not_ge hnot
      let gap : ℝ := a - sSup (Set.range (fun t : ℝ≥0 => D p t))
      have hgap : 0 < gap := by dsimp [gap]; linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / gap)
      have hinv : 1 / ((n : ℝ) + 1) < gap := by
        apply (div_lt_iff₀ (by positivity)).2
        calc
          1 = (1 / gap) * gap := by field_simp [ne_of_gt hgap]
          _ < ((n : ℝ) + 1) * gap := mul_lt_mul_of_pos_right (by exact lt_trans hn (by norm_num)) hgap
          _ = gap * ((n : ℝ) + 1) := by ring
      obtain ⟨r, hr, hnear⟩ := htouch.2 n
      have : a - 1 / ((n : ℝ) + 1) < D p ⟨(r : ℝ), hr.le⟩ := by
        rw [(show eval (D p) r = a - D p ⟨(r : ℝ), hr.le⟩ by simp [eval, brownianUpperConditionedPositiveRationalEvals, brownianUpperConditionedPositivePath, max_eq_left hr.le])] at hnear
        linarith
      have : D p ⟨(r : ℝ), hr.le⟩ ≤
          sSup (Set.range (fun t : ℝ≥0 => D p t)) :=
        le_csSup ⟨a, fun z hz => by rcases hz with ⟨t, rfl⟩; exact hweak t⟩ (Set.mem_range_self (⟨(r : ℝ), hr.le⟩ : ℝ≥0))
      dsimp [gap] at hinv
      linarith
    exact le_antisymm hle hge
  exact (by rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned B ν a hν ha]; rw [Measure.map_apply hEval measurableSet_brownianPositiveRationalTouchZero]; exact (by rw [brownianBelowConditionedLaw, Measure.smul_apply, smul_eq_mul, Measure.map_apply hD hA, Measure.restrict_apply (hD hA)]; rw [(measure_mono_null Set.inter_subset_left (measure_mono_null hsubset hmaxzero))]; simp))

end DOZZ.Proofs

end
