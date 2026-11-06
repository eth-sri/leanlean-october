module

public import NearlyMinimax.DyadicMeasurability
public import RoughRegime.Macro
public import NearlyMinimax.AnchoredCard
public import RoughRegime.Notation

𝗍

/-! The three original U2 conclusions for the actual population coefficients,
with feature nonemptiness derived from the paper's s>1 regime. -/

open Set Matrix
𝚪
𝚨

theorem anchoredIndex_nonempty_of_one_lt_smoothness (C : ModelConstants d)
    (hs : 𝘎) : Nonempty 𝘘 := by
  have horder : 0 < C.order := by
    by_contra h
    have hz : C.order = 0 := 𝖡₃
    have hle := C.smoothness_le_order_add_one
    simp only [hz, Nat.cast_zero] at hle
    linarith
  exact anchoredIndex_nonempty C.dimension_pos horder
