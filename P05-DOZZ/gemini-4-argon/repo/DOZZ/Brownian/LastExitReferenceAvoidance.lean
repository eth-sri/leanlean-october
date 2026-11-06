/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitReferenceKernel
public import DOZZ.Brownian.ConditionedFutureHistoryAvoidance
public import DOZZ.Brownian.Williams.MaximumGeometry

/-!
# The deterministic-time avoidance identity

The rational future kernel of the entrance process agrees almost everywhere with the explicit
Brownian reference kernel. This module transfers the all-path Brownian avoidance shift to that
kernel; the only distinction between rational and real-time strict avoidance is a null maximum
level, excluded by the atomless drifted-maximum law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Strict upper survival at positive rational times. -/
def brownianPositiveRationalBelow (a : ℝ) : Set BrownianPath :=
  ⋂ r : ℚ, if hr : 0 < (r : ℝ) then
    {q | q ⟨(r : ℝ), hr.le⟩ < a} else Set.univ


/-- Evaluation of a continuous path at rational times, with nonpositive coordinates set to time
zero. -/
noncomputable def brownianPathRationalEvals (q : BrownianPath) : ℚ → ℝ :=
  fun r => q ⟨max (r : ℝ) 0, le_max_right _ _⟩

theorem measurable_brownianPathRationalEvals :
    Measurable brownianPathRationalEvals := by
  apply measurable_pi_iff.mpr
  intro r
  exact ContinuousMap.measurable_eval
    (⟨max (r : ℝ) 0, le_max_right _ _⟩ : ℝ≥0)


/-- The rational and real-time strict survival events agree under the upper-conditioned reference
law. A path in their difference would have global drifted maximum exactly at the barrier. -/
theorem brownianBelowConditionedLaw_rational_below_ae
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (ν a x : ℝ) (hν : 0 < ν) (ha : 0 < a) (hax : a < x) :
    ∀ᵐ q ∂brownianBelowConditionedLaw B ν x,
      q ∈ brownianPositiveRationalBelow a ↔ q ∈ brownianPathStrictlyBelow a := by
  have rational_strict_below_implies_weak_all_times (q : BrownianPath) {a : ℝ} (ha : 0 < a) (hq0 : q 0 = 0) (hq : ∀ r : ℚ, ∀ hr : 0 < (r : ℝ), q ⟨(r : ℝ), hr.le⟩ < a) (t : ℝ≥0) : q t ≤ a := by
    by_contra hnot
    have hgt : a < q t := lt_of_not_ge hnot
    have htpos : 0 < (t : ℝ) := by
      by_contra h
      have : t = 0 := by
        apply Subtype.ext
        exact le_antisymm (le_of_not_gt h) t.2
      subst t
      simp [hq0] at hgt
      linarith
    let F : ℝ → ℝ := fun r => q ⟨max r 0, le_max_right r 0⟩
    have hF_eval (r : ℝ) (hr : 0 ≤ r) : F r = q ⟨r, hr⟩ := by
      change q ⟨max r 0, le_max_right r 0⟩ = q ⟨r, hr⟩
      congr 1
      exact Subtype.ext (max_eq_left hr)
    let U : Set ℝ := {r | 0 < r ∧ a < F r}
    have htU : (t : ℝ) ∈ U := by
      change 0 < (t : ℝ) ∧ a < F (t : ℝ)
      refine ⟨htpos, ?_⟩
      rw [hF_eval (t : ℝ) t.2]
      exact hgt
    obtain ⟨r, hrU⟩ := Rat.denseRange_cast.exists_mem_open (isOpen_Ioi.inter (isOpen_Ioi.preimage (show Continuous F by apply q.continuous.comp; exact (continuous_max.comp (continuous_id.prodMk continuous_const)).subtype_mk (fun r => le_max_right r 0)))) ⟨t, htU⟩
    have hr : 0 < (r : ℝ) ∧ a < F (r : ℝ) := by
      change (r : ℝ) ∈ U at hrU
      exact hrU
    linarith [(hq r hr.1), hr.2, ((hF_eval (r : ℝ) hr.1.le).trans (congrArg q (Subtype.ext rfl)))]
  have measurableSet_brownianPositiveRationalBelow : MeasurableSet (brownianPositiveRationalBelow a) := by
    unfold brownianPositiveRationalBelow
    apply MeasurableSet.iInter
    intro r
    by_cases hr : 0 < (r : ℝ)
    · simp only [dite_eq_left hr]
      exact measurableSet_lt (ContinuousMap.measurable_eval
        (⟨(r : ℝ), hr.le⟩ : ℝ≥0))
        measurable_const
    · simp [hr]
  have _ := hax
  classical
  let D : BrownianPath → BrownianPath := driftedBrownianPath (-ν)
  let R : Set BrownianPath := brownianPositiveRationalBelow a
  let S : Set BrownianPath := brownianPathStrictlyBelow a
  have hR := measurableSet_brownianPositiveRationalBelow
  have hS := measurableSet_brownianPath_below a
  have hdiff : MeasurableSet (R \ S) := hR.diff hS
  have hD : Measurable D := continuous_driftedBrownianPath.measurable.comp
    (measurable_const.prodMk measurable_id)
  let _ := noAtoms_brownianMaximumReferenceLaw ν
  have hmaxzero : B {p | driftedBrownianMaximum ν p = a} = 0 := by
    have hsingle := congrArg (fun m : Measure ℝ => m {a}) (brownianPath_globalMaximum_map B hB ν hν)
    rw [Measure.map_apply_of_aemeasurable (aemeasurable_driftedBrownianMaximum B hB ν hν) (measurableSet_singleton a)] at hsingle
    simpa only [Set.preimage, mem_singleton_iff, eq_comm, measure_singleton] using hsingle
  have hrawae : ∀ᵐ p ∂B, p ∉ D ⁻¹' (R \ S) := by
    filter_upwards [(show ∀ᵐ p ∂B, driftedBrownianMaximum ν p ≠ a by apply ae_iff.mpr; simpa only [not_not] using hmaxzero), hB.eval_zero_ae_eq_zero] with p hmax hp0
    intro hp
    change D p ∈ R \ S at hp
    have hrat : ∀ r : ℚ, ∀ hr : 0 < (r : ℝ),
        D p ⟨(r : ℝ), hr.le⟩ < a := by
      intro r hr
      have h := (show ∀ r : ℚ, D p ∈ (if hr : 0 < (r : ℝ) then {q | q ⟨(r : ℝ), hr.le⟩ < a} else Set.univ) by simpa only [R, brownianPositiveRationalBelow, Set.mem_iInter] using hp.1) r
      simp only [hr, dite_eq_left, Set.mem_ofPred_eq] at h
      exact h
    have hweak := rational_strict_below_implies_weak_all_times (D p) ha (by
      simp [D, driftedBrownianPath, hp0]) hrat
    have ⟨t, ht⟩ : ∃ t : ℝ≥0, a ≤ D p t := by
      by_contra hn
      apply hp.2
      intro t
      exact lt_of_not_ge (fun h => hn ⟨t, h⟩)
    have hbound : BddAbove (Set.range (fun t : ℝ≥0 => D p t)) :=
      ⟨a, fun z hz => by
        rcases hz with ⟨u, rfl⟩
        exact hweak u⟩
    have hsup : driftedBrownianMaximum ν p =
        sSup (Set.range (fun u : ℝ≥0 => D p u)) := by
      unfold driftedBrownianMaximum
      congr 1
      ext z
      constructor
      · rintro ⟨u, rfl⟩
        refine ⟨u, ?_⟩
        simp [D, driftedBrownianPath, neg_mul, sub_eq_add_neg]
      · rintro ⟨u, hu⟩
        refine ⟨u, ?_⟩
        simpa [D, driftedBrownianPath, neg_mul, sub_eq_add_neg] using hu
    have hle : driftedBrownianMaximum ν p ≤ a := by
      rw [hsup]
      exact csSup_le (Set.range_nonempty _) (by
        rintro z ⟨u, rfl⟩
        exact hweak u)
    have hge : a ≤ driftedBrownianMaximum ν p := by
      calc
        a = D p t := (le_antisymm (hweak t) ht).symm
        _ ≤ sSup (Set.range (fun u : ℝ≥0 => D p u)) := le_csSup hbound (Set.mem_range_self t)
        _ = driftedBrownianMaximum ν p := hsup.symm
    exact hmax (le_antisymm hle hge)
  have hraw : B (D ⁻¹' (R \ S)) = 0 := by
    have hraw' := ae_iff.mp hrawae
    rw [(show {p | ¬ p ∉ D ⁻¹' (R \ S)} = D ⁻¹' (R \ S) by ext p; simp)] at hraw'
    exact hraw'
  filter_upwards [(by apply ae_iff.mpr; rw [(show {q | ¬ q ∉ R \ S} = R \ S by ext q; simp)]; exact (by rw [brownianBelowConditionedLaw, Measure.smul_apply, smul_eq_mul, Measure.map_apply hD hdiff, Measure.restrict_apply (hD hdiff)]; rw [(measure_mono_null (Set.inter_subset_left) hraw)]; simp))] with q hq
  constructor
  · intro hR
    by_contra hS
    exact hq ⟨hR, hS⟩
  · intro hS
    simp only [brownianPositiveRationalBelow, Set.mem_iInter]
    intro r
    by_cases hr : 0 < (r : ℝ)
    · simp only [hr, dite_eq_left, Set.mem_ofPred_eq]
      simpa [brownianPathStrictlyBelow] using hS ⟨(r : ℝ), hr.le⟩
    · simp [hr]

end DOZZ.Proofs

end
