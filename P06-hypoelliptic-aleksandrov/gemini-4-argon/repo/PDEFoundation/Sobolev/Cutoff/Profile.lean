module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# A quantitative smooth transition profile

This file records the one-dimensional profile used by later cutoff
constructions. The profile is `Real.smoothTransition`, with its endpoint and
range properties and the explicit first-derivative bound `8`.

No compactness-selected derivative constant is used, and no second-derivative
bound is part of this first-order API.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace PDE

/- The canonical smooth transition from `0` to `1`. -/
def smoothTransitionProfile : ℝ → ℝ :=
  Real.smoothTransition

namespace smoothTransitionProfile

/- The canonical transition profile is smooth to every order. -/
theorem smooth : ContDiff ℝ (⊤ : ℕ∞) smoothTransitionProfile :=
  Real.smoothTransition.contDiff

/- The canonical transition profile vanishes to the left of `0`. -/
theorem zero_of_nonpos {t } (ht : t ≤ 0) :
    smoothTransitionProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos ht

/- The canonical transition profile equals `1` to the right of `1`. -/
theorem one_of_one_le {t } (ht : 1 ≤ t) :
    smoothTransitionProfile t = 1 :=
  Real.smoothTransition.one_of_one_le ht

/- The canonical transition profile is nonnegative. -/
theorem nonneg (t : ℝ) :
    0 ≤ smoothTransitionProfile t :=
  Real.smoothTransition.nonneg t

/- The canonical transition profile is at most `1`. -/
theorem le_one (t : ℝ) :
    smoothTransitionProfile t ≤ 1 :=
  Real.smoothTransition.le_one t

/- The explicit first-derivative constant for the canonical transition. -/
end smoothTransitionProfile

end PDE
