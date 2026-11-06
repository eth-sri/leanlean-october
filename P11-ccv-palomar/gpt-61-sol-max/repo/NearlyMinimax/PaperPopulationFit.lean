module

public import NearlyMinimax.DyadicMeasurability
public import NearlyMinimax.AnchoredCard

@[expose] public section

/-! The three original U2 conclusions for the actual population coefficients,
with feature nonemptiness derived from the paper's s>1 regime. -/

noncomputable section
open Set Matrix
open scoped BigOperators
namespace NearlyMinimax

theorem anchoredIndex_nonempty_of_one_lt_smoothness {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) : Nonempty (AnchoredIndex d C.order) := by
  have horder : 0 < C.order := by
    by_contra h
    have hz : C.order = 0 := by omega
    have hle := C.smoothness_le_order_add_one
    simp only [hz, Nat.cast_zero, zero_add] at hle
    linarith
  exact anchoredIndex_nonempty C.dimension_pos horder

end NearlyMinimax
