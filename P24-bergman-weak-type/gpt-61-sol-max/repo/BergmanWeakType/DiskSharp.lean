/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.WeightedSharp
import BergmanWeakType.Boundary.Concentration







namespace BergmanWeakType

theorem positiveProjection_constant_eq_one : weakTypeConstant diskArea positiveProjection = 1 := by
  have h := weightedPositiveProjection_constant_eq 0 (neg_one_lt_zero)
  unfold weightedPositiveProjection at h
  unfold positiveProjection
  simpa using h

theorem projection_constant_eq_one :
    weakTypeConstant diskArea (fun f z ↦ ‖projection f z‖ₑ) = 1 :=
  le_antisymm
    (by simpa [weightedProjection, projection] using weightedProjection_constant_le 0 (neg_one_lt_zero))
    (by simpa [weightedProjection, projection] using one_le_weightedProjection_constant 0 (neg_one_lt_zero))

end BergmanWeakType
