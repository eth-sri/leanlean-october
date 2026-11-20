/- Native literal endpoint propositions. No endpoint theorem is assumed. -/
module

public import Glennie.Native
@[expose] public section

namespace Glennie.SubmissionR03
noncomputable section

def quatI : Quaternion ℝ := ⟨0,1,0,0⟩
def quatJ : Quaternion ℝ := ⟨0,0,1,0⟩
def quatK : Quaternion ℝ := ⟨0,0,0,1⟩
def octI : Octonion := (quatI,0)
def octK : Octonion := (quatK,0)
def octL : Octonion := (0,1)
def octJL : Octonion := (0,quatJ)
def witnessZ : Albert := ⟨0,0,0,octJL,-octL,-octK⟩
def witnessX : Albert := ⟨-1,0,1,0,0,0⟩
def witnessY : Albert := ⟨0,0,0,octScalar 1,octI,octScalar 1⟩
def nativeMarks : Fin 3 → Albert := ![witnessX,witnessY,witnessZ]

end
end Glennie.SubmissionR03

namespace Glennie
export SubmissionR03 (quatI quatJ quatK octI octK octL octJL witnessX witnessY witnessZ)
end Glennie
