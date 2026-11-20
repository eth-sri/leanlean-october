module

public import Glennie.Theorems.Frames
public import Glennie.Automorphism
/- The polynomial reconstruction from a frame encoder. -/

@[expose] public section
noncomputable section


namespace Glennie.SubmissionR03

def projectorFrame (x : Albert) : Fin 3 → Albert :=
  ![(1 / (Nat.cast 2 : ℝ)) • (jordan x x - x), 1 - jordan x x,
    (1 / (Nat.cast 2 : ℝ)) • (jordan x x + x)]
end Glennie.SubmissionR03

namespace Glennie

export SubmissionR03 (projectorFrame)

theorem projectorFrame_encoder (x : Albert) : encoder (projectorFrame x)=x := by
  simp [encoder, projectorFrame]
  module

theorem frame_as_projector (p : Fin 3 → Albert) (hp : Frame p) :
    p = projectorFrame (encoder p) := by
  funext i
  fin_cases i <;> simp [projectorFrame, ← hp.sum_unit] <;>
    rw [frame_encoder_square p hp] <;> (try unfold encoder) <;> module

theorem compactAutomorphism_projectorFrame (g : CompactAutomorphism) (x : Albert) (i : Fin 3) :
    g.equiv (projectorFrame x i) = projectorFrame (g.equiv x) i := by
  fin_cases i <;> simp [projectorFrame, g.map_jordan, g.map_unit]

end Glennie
