module
import Mathlib
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








