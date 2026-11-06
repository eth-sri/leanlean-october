/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitShiftLaw
public import DOZZ.Brownian.ConditionedPathSupport
public import DOZZ.Brownian.Reflection.LastCut
import DOZZ.Brownian.Reflection.Entrance

/-! The last-cut ordering required by the lower Williams tail estimate. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- A path that stays below `-d` after its last exit cannot subsequently hit a higher level. -/
theorem last_exit_le_of_post_nonpos (p : BrownianPath) (c d : ℝ) (hcd : c ≤ d)
    (hp : ∀ t : ℝ≥0, negativeConditionedPostLastExitPath d p t ≤ 0) :
    negativeLastExitTime p c ≤ negativeLastExitTime p d := by
  rcases lt_or_eq_of_le hcd with hlt | heq
  · have hhit (u : ℝ≥0) (hu : p u = -c) : u ≤ negativeLastExitTime p d := by
      by_contra hnot
      have h := hp (u-negativeLastExitTime p d)
      change p _+d ≤ 0 at h
      rw [add_tsub_cancel_of_le (lt_of_not_ge hnot).le, hu] at h
      linarith
    apply (negativeLastExitTime_le_iff_no_future_visit p c _
      ⟨negativeLastExitTime p d, hhit⟩).mpr
    grind
  simp_all

/-- For each fixed pair of levels the conditioned last exits are ordered almost surely.
Only the proved post-last-exit law and path support are consumed. -/
theorem conditioned_last_exit_mono_ae (ν c d : ℝ) (hν : 0 < ν)
    (hd : 0 < d) (hcd : c ≤ d) (P : Measure BrownianPath)
    (hP : IsNegativeConditionedBrownianLaw ν P) :
    ∀ᵐ p ∂P, negativeLastExitTime p c ≤ negativeLastExitTime p d := by
  have hlaw := negativeConditioned_postLastExit_law ν d hν hd P hP
  have hclosed : IsClosed {p : BrownianPath | ∀ t : ℝ≥0, p t ≤ 0} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro t
    exact isClosed_le (by fun_prop) continuous_const
  have hp : ∀ᵐ p ∂P.map (negativeConditionedPostLastExitPath d), ∀ t : ℝ≥0, p t ≤ 0 := by
    rw [hlaw.2]
    exact DOZZ.Proofs.isNegativeConditionedBrownianLaw_ae_nonpos hP
  filter_upwards [((ae_map_iff hlaw.1 hclosed.measurableSet).mp hp)] with p hp
  exact last_exit_le_of_post_nonpos p c d hcd hp

end DOZZ.Proofs
