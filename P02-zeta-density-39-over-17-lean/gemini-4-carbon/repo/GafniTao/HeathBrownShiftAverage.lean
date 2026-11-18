module
public import GafniTao.HeathBrownKthDerivativeSetup
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred

@[expose] public section

/-!
# Heath-Brown Lemma 1: exact translation average

The first step in Heath-Brown's proof averages `H` translates of the
exponential sum.  This file proves the exact finite identity and the complete
endpoint loss.  No differentiability or mean-value estimate is used here.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The translate by `h` of Heath-Brown's positive-index exponential sum. -/
noncomputable def heathBrownShiftedExponentialSum
    (N : ℕ) (f : ℝ → ℝ) (h : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, heathBrownPhase (f ((n + h : ℕ) : ℝ))

end

end GafniTao
