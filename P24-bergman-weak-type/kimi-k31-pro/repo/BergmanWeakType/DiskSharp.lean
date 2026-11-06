module

public import BergmanWeakType.Reproduction
public import BergmanWeakType.WeightedSharp

/-! # Sharp weak type constants on the unit disk -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace BergmanWeakType

/-- The positive Bergman projection has weak type bound one on the unit disk. -/
theorem isWeakTypeBound_positiveProjection_one :
    IsWeakTypeBound diskArea positiveProjection 1 := by
  have h := isWeakTypeBound_weightedPositiveProjection (α := 0) (by norm_num)
  have hz : weightedPositiveProjection 0 = positiveProjection := by
    funext f z
    simp [weightedPositiveProjection, positiveProjection, weightedKernel_zero]
  rw [hz] at h
  simpa [weightedArea, gammaConstant] using h

/-- The sharp weak type constant of the positive disk Bergman projection is one. -/
theorem positiveProjection_constant_eq_one : weakTypeConstant diskArea positiveProjection = 1 :=
  le_antisymm (weakTypeConstant_le_of_bound isWeakTypeBound_positiveProjection_one)
    (one_le_projection_constant.trans projection_constant_le_positiveProjection_constant)

/-- The sharp weak type constant of the complex disk Bergman projection is one. -/
theorem projection_constant_eq_one :
    weakTypeConstant diskArea (fun f z ↦ ‖projection f z‖ₑ) = 1 := by
  apply le_antisymm _ one_le_projection_constant
  exact projection_constant_le_positiveProjection_constant.trans_eq
    positiveProjection_constant_eq_one

end BergmanWeakType
