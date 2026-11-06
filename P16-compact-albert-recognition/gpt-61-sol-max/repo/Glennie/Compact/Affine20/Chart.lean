/- Reconstruction of a complete ordered-frame ledger from its twenty coordinates. -/
module
public import Glennie.Compact.ObservationScript
public import Glennie.Theorems.Frames
public import Glennie.LinearSimp
@[expose] public section
namespace Glennie.Compact.Affine20
noncomputable section
set_option maxHeartbeats 2000000
export Glennie.SubmissionR03 (ext3 lift4 lift8 centred encode20 decP decQ decR decC decode20)

theorem decode_encode_frames (T : Triple) (hT : ∀ a, Frame (T a)) :
    decode20 (encode20 (ledger54 T)) = ledger54 T := by
  have hs (f) : T f 2 = 1 - T f 0 - T f 1 := by
    rw [← (hT f).sum_unit]
    module
  have ht (f i) : trace (T f i) = 1 := (hT f).trace_one i
  ext i j k <;> fin_cases i <;> fin_cases j <;> (try fin_cases k) <;>
    norm_num [decode20, decC, decP, decQ, decR, lift8, lift4, ext3, encode20,
      centred, Glennie.SubmissionR03.f0, Glennie.SubmissionR03.f1,
      ledger54, ledger, inner, hs, albert_linear, jordan_unit_left, jordan_unit_right,
      trace_unit, ht, jordan_comm] <;> ring
end
end Glennie.Compact.Affine20
