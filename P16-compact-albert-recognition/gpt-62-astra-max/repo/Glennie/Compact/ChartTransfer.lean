module

public import Glennie.Compact.FlowFamily

public import Glennie.Compact.Affine20.Chart
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Real
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Module

@[expose] public section

namespace Glennie.Compact.ChartTransfer

open Glennie.Compact.Affine20 Glennie.Compact.FlowFamily

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

local macro "chart_arith" : tactic => `(tactic|
  (norm_num [decode20, encode20, decC, decP, decQ, decR, centred, lift4, lift8, ext3] <;> ring))

theorem encode20_decode20 (v : Fin 20 → ℝ) : encode20 (decode20 v) = v := by
  funext i; fin_cases i <;> chart_arith

def cRow (L : Ledger54) : Fin 20 → ℝ := fun r =>
  L.1 (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2

/-- `rowsOf` reads the same twenty cells of a decoded chart point: the affine map from chart
coordinates to C-row coordinates. -/
def rowsOf (v : Fin 20 → ℝ) : Fin 20 → ℝ := cRow (decode20 v)

theorem rowsOf_encode20 (L : Ledger54) (h : InDomain L) : rowsOf (encode20 L) = cRow L :=
  congrArg cRow (decode_encode L h)

theorem continuous_rowsOf : Continuous rowsOf := by
  have hc : Continuous cRow := by unfold cRow; fun_prop
  exact hc.comp continuous_decode20

/-- Read the three marginal sums through each head cell. Only the twenty cells
in `rowIndex` occur in these sums; the placeholders at the other seven cells
are never read by the chart encoder. -/
def chartVec (c : Fin 20 → ℝ) : Fin 20 → ℝ :=
  let slot := ![![![0,1,2],![3,4,5],![6,7,0]], ![![8,9,10],![11,12,13],![14,15,0]],
    ![![16,17,0],![18,19,0],![0,0,0]]]
  let t i j k := c (slot i j k)
  let sum (f : Fin 3 → ℝ) := f 0 + f 1 + f 2
  encode20 (t, fun i j => sum (t i j), fun j k => sum (t · j k), fun k i => sum (t i · k))

theorem chartVec_rowsOf (v : Fin 20 → ℝ) : chartVec (rowsOf v) = v := by
  funext r; fin_cases r <;>
    norm_num [chartVec, rowsOf, cRow, rowIndex, decode20, encode20, decC, decP, decQ, decR,
      centred, lift4, lift8, ext3] <;> ring

theorem rowsOf_motion (T : Frames3) (hT : ∀ a, Frame (T a)) (s : Param) :
    rowsOf (encode20 (fullLedger (motion T s))) = rowLedger T s :=
  rowsOf_encode20 _ (ledger54_inDomain _ (motion_frame T hT s))

theorem encode_motion (T : Frames3) (hT : ∀ a, Frame (T a)) (s : Param) :
    encode20 (fullLedger (motion T s)) = chartVec (rowLedger T s) := by
  rw [← rowsOf_motion T hT s, chartVec_rowsOf]

end
end Glennie.Compact.ChartTransfer
