module

public import PottsDiscontinuity.SixVertex.InfinitySupport
public import PottsDiscontinuity.SixVertex.InfinityMoves

/-! # Admissible labelled defect choices and their upper row -/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N n : ℕ}

section
variable (x : Finset (Fin N))
include x

/-- Defects indexed by their actual cyclic sites. -/
abbrev DefectSite := {i : Fin N // i ∈ defects x}

/-- `true` chooses a left unit move and `false` a right unit move. -/
abbrev DefectChoice := DefectSite x → Bool

end

/-- A right-then-left choice at adjacent defects would exchange them and is forbidden. -/
def AdmissibleDefectChoice {x : Finset (Fin N)} (d : DefectChoice x) : Prop :=
  ∀ i : DefectSite x, ∀ hj : nxt i.1 ∈ defects x,
    d i = false → d ⟨nxt i.1, hj⟩ = false

variable (hn : 0 < n) (x : IndependentState N n)
include hn

end PottsDiscontinuity.SixVertex
