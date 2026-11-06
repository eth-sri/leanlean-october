/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
/-! The explicit-`rpow` form of the standard positive-real conversion rule. -/
public section
namespace DOZZ.Proofs

/-- Convert a positive real power without first changing the explicit `rpow` head. -/
theorem ennreal_rpow_ofReal_pos {x p : ℝ} (hx : 0 < x) :
    ENNReal.rpow (ENNReal.ofReal x) p = ENNReal.ofReal (x ^ p) :=
  ENNReal.ofReal_rpow_of_pos hx

end DOZZ.Proofs
