module

public import Glennie.Compact.FlowFamily
public import Glennie.Compact.FrameTopology
@[expose] public section

namespace Glennie.Compact.ChartTransfer

open Glennie.Compact.Affine20 Glennie.Compact.FlowFamily

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem decode20_inDomain (v : Fin 20 → ℝ) : InDomain (decode20 v) := by
  constructor <;> (intro i; fin_cases i) <;> (try (intro j; fin_cases j)) <;>
    simp [decode20, decC, decP, decQ, decR, lift4, lift8, ext3] <;> ring

theorem encode20_decode20 (v : Fin 20 → ℝ) : encode20 (decode20 v) = v := by
  funext n
  fin_cases n <;> simp [encode20, centred, decode20, decC, decP, decQ, decR, lift4, lift8, ext3] <;> ring

/-- The twenty selected triple traces, read either from a ledger or its chart. -/
def cRow (L : Ledger54) : Fin 20 → ℝ := fun r =>
  L.1 (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2

def rowsOf (v : Fin 20 → ℝ) : Fin 20 → ℝ := cRow (decode20 v)

@[fun_prop] private theorem continuous_ext3 {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) (i : Fin 3) :
    Continuous (fun x => ext3 (f x) (g x) i) := by
  fin_cases i <;> dsimp [ext3] <;> fun_prop

theorem continuous_decode20 : Continuous decode20 := by
  unfold decode20 decC decP decQ decR lift4 lift8
  fun_prop

theorem continuous_rowsOf : Continuous rowsOf := by exact (by unfold cRow; fun_prop : Continuous cRow).comp continuous_decode20

/-- The selected rows already separate all affine chart points. -/
theorem rowsOf_injective : Function.Injective rowsOf := by
  intro x y h
  have H := congrFun h
  simp [Fin.forall_fin_succ, rowsOf, cRow, rowIndex, decode20,
    decC, decP, decQ, decR, lift4, lift8, ext3] at H
  funext i
  fin_cases i <;> grind

/-- The moved triple of the family, as one object. -/
def movedTriple (T : Fin 3 → Fin 3 → Albert) (s : Fin 20 → ℝ) : Fin 3 → Fin 3 → Albert :=
  fun a => movedFrame contextDirection T a s

theorem movedTriple_zero (T : Fin 3 → Fin 3 → Albert) : movedTriple T 0 = T := by
  funext a
  exact movedFrame_zero contextDirection T a

/-- Every moved frame is a frame, by the `FlowFamily.movedFrame_frame`
(FlowFamily.lean). -/
theorem movedTriple_frame (T : Fin 3 → Fin 3 → Albert) (hT : IsFrameTriple T)
    (s : Fin 20 → ℝ) (a : Fin 3) : Frame (movedTriple T s a) :=
  movedFrame_frame contextDirection T contextDirection_isJordanDerivation
    contextDirection_traceFree a (hT a) s

theorem rowsOf_encode20_movedTriple (T : Triple) (hT : IsFrameTriple T) (s : Fin 20 → ℝ) :
    rowsOf (encode20 (ledger54 (movedTriple T s))) = rowLedger T s := by
  rw [rowsOf, decode_encode_frames _ (movedTriple_frame T hT s)]
  rfl

end
end Glennie.Compact.ChartTransfer
