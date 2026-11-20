module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Basic.Complex.Basic

@[expose] public section

namespace OAI.SevenEighths

/-- The compactly supported left and right test functions for the Mellin transforms,
together with positive lower endpoints of their support intervals. -/
structure MellinWindows where
  left : SchwartzMap ℝ ℂ
  right : SchwartzMap ℝ ℂ
  leftLo : ℝ
  leftHi : ℝ
  rightLo : ℝ
  rightHi : ℝ
  left_pos : 0 < leftLo
  right_pos : 0 < rightLo
  left_support : Function.support left ⊆ Set.Icc leftLo leftHi
  right_support : Function.support right ⊆ Set.Icc rightLo rightHi

end OAI.SevenEighths
