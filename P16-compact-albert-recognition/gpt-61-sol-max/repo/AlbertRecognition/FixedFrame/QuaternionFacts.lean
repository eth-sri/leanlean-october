/- Finite quaternion coordinate lemmas for the compact native spin commutant.
No octonion associativity or classification theorem is used. -/
module

public import Glennie.Native

@[expose] public section

namespace AlbertRecognition.FixedFrame
noncomputable section

open scoped Quaternion

def qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩
def qj : Quaternion ℝ := ⟨0, 0, 1, 0⟩
def qk : Quaternion ℝ := ⟨0, 0, 0, 1⟩


end
end AlbertRecognition.FixedFrame
