module

public import NearlyMinimax.PilotCoordinateExpansion
public import NearlyMinimax.KernelMomentBounds
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Genuine clipped dyadic grid nesting, including the cube's right boundary. -/
𝚫
𝚨

𝗇 𝔅 𝘯 z = 𝘯 x
theorem regular_grid_same_cell_congr (h : k = l) hk hl
    (x z : Covariate d) : 𝔅 ↔
       regularGridCell l hl z = regularGridCell l hl x := by
  subst l
  rfl

𝗇 𝔄 2 * k
𝗇 𝔇 (𝔄 : ℕ) * x
theorem regular_grid_index_parent k hk x :
    (regularGridIndex 𝔄  𝖡₃  x).val / 2 = (regularGridIndex k hk x).val := by
  have hre : 𝔇 = 𝘘₁ * 𝗟 := by push_cast; ring
  have hf : ⌊𝔇⌋₊ / 2 = ⌊𝘘₁⌋₊ := by
    rw [hre, Nat.mul_cast_floor_div_cancel 𝖨₃ ]
  simp only [regularGridIndex]
  omega

/-- A genuine fine-cell equality implies equality of the dyadic parent labels. -/
theorem regular_grid_cell_parent_eq k hk
    (x z : Covariate d)
    (h : regularGridCell 𝔄  𝖡₃  z = regularGridCell 𝔄  𝖡₃  x) :
    𝔅 := by
  funext i
  apply Fin.ext
  have hi := congrArg (fun c => (c i).val / 2) h
  change (regularGridIndex 𝔄  𝖡₃  $ z i ).val / 2 =
    (regularGridIndex 𝔄  𝖡₃  $ x i ).val / 2 at hi
  rw [regular_grid_index_parent k hk, regular_grid_index_parent k hk] at hi
  exact hi

theorem dyadicPilotCell_subset_parent j (x : Covariate d) :
    dyadicPilotCell j x ⊆ dyadicPilotCell 𝘮 x := by
  cases j with
  | zero => simp
  | succ j =>
    intro z hz
    apply regular_grid_cell_parent_eq 𝘷  𝖠₃  x z
    exact (regular_grid_same_cell_congr  𝖡₃   𝖠₃   𝖠₃  x z).mp hz
