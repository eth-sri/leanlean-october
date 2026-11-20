module

public import Glennie.Native.CubicIdentity
public import Glennie.ObservationLaws
public import Glennie.Theorems.Frames

/- Polynomial projectors for trace-zero norm-two cubic-norm-zero elements.
   These are derived from the native cubic residual and Jordan identity. -/

@[expose] public section
namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000

export _root_.Glennie.SubmissionR03 (projectorFrame)

theorem projectorFrame_encoder (x : Albert) : encoder (projectorFrame x)=x := by
  simp [encoder, projectorFrame] <;> module

end
end Glennie
