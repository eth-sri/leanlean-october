module

public import GS.Core

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Perfect shuffle, expressed using pair coordinates before flattening.
The pair (r,s) is the manuscript's scalar coordinate r*b+s.
 -/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS

/-- Explicit block-diagonal embedding, useful also for shared blocks. -/
def blockMatrix {k b : ℕ} (B : Fin k → Matrix (Fin b) (Fin b) ℝ) :
    Matrix (Fin k × Fin b) (Fin k × Fin b) ℝ :=
  fun i j => if i.1 = j.1 then B i.1 i.2 j.2 else 0

end GS
