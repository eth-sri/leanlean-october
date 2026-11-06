/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.WeightedSharp
public import BergmanWeakType.Reproduction

/-! # Sharp weak type constants on the unit disk

The unweighted results are the specializations of the sharp weighted results to exponent `α = 0`.
-/

@[expose] public section

noncomputable section

namespace BergmanWeakType

/-- The positive unweighted constant is the weighted constant at `α = 0`. -/
theorem positiveProjection_constant_eq_one : weakTypeConstant diskArea positiveProjection = 1 := by
  rw [← weightedPositiveProjection_constant_zero,
    weightedPositiveProjection_constant_eq 0 (by norm_num)]
  simp [gammaConstant]

/-- The positive disk projection has weak type bound one. -/
theorem isWeakTypeBound_positiveProjection_one :
    IsWeakTypeBound diskArea positiveProjection 1 := by
  have h := isWeakTypeBound_weightedPositiveProjection (α := 0) (by norm_num)
  rw [weightedArea_zero, show weightedPositiveProjection 0 = positiveProjection from
    funext weightedPositiveProjection_zero] at h
  simpa [gammaConstant] using h

/-- The sharp weak type constant of the complex disk Bergman projection is one. -/
theorem projection_constant_eq_one :
    weakTypeConstant diskArea (fun f z ↦ ‖projection f z‖ₑ) = 1 :=
  le_antisymm (projection_constant_le_positiveProjection_constant.trans_eq
    positiveProjection_constant_eq_one) one_le_projection_constant

end BergmanWeakType
