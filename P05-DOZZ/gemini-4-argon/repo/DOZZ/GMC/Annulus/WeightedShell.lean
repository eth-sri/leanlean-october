/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GmcMassMoment
public import DOZZ.GMC.Moments.ExactScaleBallMoment
public import DOZZ.GMC.Moments.PositiveExponent
public import DOZZ.GMC.Construction.GMCMeasurableVersion
public import DOZZ.GMC.FieldChaosMultiNegativePower

/-!
# Weighted annulus comparisons

An annulus excludes its center, so its radial weight is bounded above and below at every
real insertion exponent. The same deterministic comparison must reverse when taking a
negative moment. The Gaussian scale exponent retains the actual moment order throughout.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- The true Gaussian scale exponent equals the polynomial in the merged exact moment law. -/
theorem gmcScaleExponent_eq_polynomial γ p (hγ : γ ≠ 0) :
    gmcScaleExponent γ p = 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2 := by
  unfold gmcScaleExponent Q
  field_simp [hγ]

end DOZZ.Proofs
