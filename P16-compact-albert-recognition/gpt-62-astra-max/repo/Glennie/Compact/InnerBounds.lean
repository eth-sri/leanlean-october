module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.GCongr
@[expose] public section
namespace Glennie.Compact
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem pair_difference (a b c d : E) : |Inner.inner ℝ a b - Inner.inner ℝ c d| ≤ ‖a-c‖*‖b‖ + ‖c‖*‖b-d‖ := by
  grw [← sub_add_sub_cancel (Inner.inner ℝ a b) (Inner.inner ℝ c b) _,
    ← _root_.inner_sub_left, ← _root_.inner_sub_right, abs_add_le, abs_real_inner_le_norm,
    abs_real_inner_le_norm]
end Glennie.Compact
