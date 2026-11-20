module
public import Glennie.Compactness
public import Glennie.Compact.Affine20.Chart
@[expose] public section
namespace Glennie.Compact.FrameTopology
open Affine20
noncomputable section

theorem continuous_ledger54 : Continuous ledger54 := by
  unfold ledger54 Glennie.SubmissionR03.fullLedger ledger
  fun_prop

theorem continuous_encode20 : Continuous encode20 := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [encode20, centred] <;> fun_prop

end
end Glennie.Compact.FrameTopology
