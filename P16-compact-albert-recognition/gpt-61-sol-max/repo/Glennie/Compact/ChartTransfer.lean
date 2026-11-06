/- Transfer between the selected triple-trace rows and the centered twenty-dimensional
chart. Finite linear arithmetic proves injectivity, without an explicit inverse. -/
module
public import AlbertGeometry.LinearSimp
public import Mathlib.Tactic.Linarith

public import Glennie.Compact.FlowFamily
public import Glennie.Compact.Affine20.Chart

@[expose] public section

namespace Glennie.Compact.ChartTransfer

open Glennie.Compact.Affine20 Glennie.Compact.FlowFamily

noncomputable section

set_option maxHeartbeats 2000000

/-! ## Zero-margin helpers for the reconstruction maps

Each is an `ext3` telescope: `x + y + (-(x + y)) = 0`. They are stated for the `Affine20.lift4` (Chart.lean) and `Affine20.lift8` (Chart.lean). -/

theorem encode20_decode20 (v : Fin 20 → ℝ) : encode20 (decode20 v) = v := by
  funext n
  fin_cases n <;>
    norm_num [encode20, decode20, centred, decC, decP, decQ, decR, lift8, lift4, ext3] <;>
    ring

/-! ## The twenty selected C rows -/

/-- The twenty `rowIndex` cells of the C block of a 54-entry ledger. -/
def cRow (L : Ledger54) : Fin 20 → ℝ := fun r =>
  L.1 (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2

/-- `rowsOf` reads the same twenty cells of a decoded chart point: the affine map from chart
coordinates to C-row coordinates. -/
def rowsOf (v : Fin 20 → ℝ) : Fin 20 → ℝ := cRow (decode20 v)



/-- On the genuine domain the two readings agree, by the `Affine20.decC_encode`
(Chart.lean). -/
theorem rowsOf_encode20 (T : Triple) (hT : ∀ a, Frame (T a)) :
    rowsOf (encode20 (ledger54 T)) = cRow (ledger54 T) :=
  congrArg cRow (decode_encode_frames T hT)

theorem continuous_rowsOf : Continuous rowsOf := by
  unfold rowsOf cRow decode20 decC decP decQ decR lift8 lift4 ext3
  fun_prop

/-- The selected rows determine every chart coordinate. -/
theorem rowsOf_injective : Function.Injective rowsOf := by
  intro v w h
  have hh := congrFun h
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero] at hh
  norm_num [rowsOf, cRow, rowIndex, decode20, decC, decP, decQ, decR,
    lift8, lift4, ext3] at hh
  funext n
  fin_cases n <;> dsimp only <;> linarith! only [hh]

/-! ## The bridge to the flowed family

`FlowFamily.rowLedger` (FlowFamily.lean) is literally `cRow` of the 54-entry ledger of the
moved triple. -/

/-- The moved triple of the family, as one object. -/
def movedTriple (T : Fin 3 → Fin 3 → Albert) (s : Fin 20 → ℝ) : Fin 3 → Fin 3 → Albert :=
  fun a => movedFrame contextDirection contextDirection_isJordanDerivation
    contextDirection_traceFree T a s

theorem movedTriple_zero (T : Fin 3 → Fin 3 → Albert) : movedTriple T 0 = T := by
  funext a
  exact movedFrame_zero contextDirection contextDirection_isJordanDerivation
    contextDirection_traceFree T a

variable (T : Fin 3 → Fin 3 → Albert) (hT : ∀ a, Frame (T a))
    (s : Fin 20 → ℝ)

include T hT s in
/-- Every moved frame is a frame, by the `FlowFamily.movedFrame_frame`
(FlowFamily.lean). -/
theorem movedTriple_frame  (a : Fin 3) : Frame (movedTriple T s a) :=
  movedFrame_frame contextDirection contextDirection_isJordanDerivation
    contextDirection_traceFree T a (hT a) s

/-- `rowLedger` is `cRow` of the moved 54-entry ledger. -/
theorem cRow_ledger54_movedTriple (T : Fin 3 → Fin 3 → Albert) (s : Fin 20 → ℝ) :
    cRow (ledger54 (movedTriple T s)) = rowLedger T s := by
  funext r
  rw [cRow, ledger54_C, rowLedger]
  rfl

include T hT s in
/-- **Chart transfer.** For a frame triple, the chart point of the moved ledger is recovered
from the twenty selected C rows. This identity indexes sections by chart
coordinates, and the reason no new 20x20 determinant is needed. -/
theorem rowsOf_encode20_movedTriple  :
    rowsOf (encode20 (ledger54 (movedTriple T s))) = rowLedger T s := by
  rw [rowsOf_encode20 _ (movedTriple_frame T hT s), cRow_ledger54_movedTriple]


end
end Glennie.Compact.ChartTransfer
