/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Statements.GFFStructure.DiskGreenKernel

/-! The definition `DOZZ.diskGreenCovariance`. -/


open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u

namespace DOZZ

/-- Zero-extension covariance on global tests, used in `exists_exteriorPinned_markov_uniform`.
The inner integral is explicitly parenthesized. Diagonal `log 0` is used only under volume. -/
noncomputable def diskGreenCovariance (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (f g : TestFn) : ℝ :=
  ∫ z in ball c ρ, f z * (∫ w in ball c ρ, diskGreenKernel c ρ hρ z w * g w)

end DOZZ
