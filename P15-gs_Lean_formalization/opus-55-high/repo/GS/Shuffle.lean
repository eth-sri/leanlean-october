module

public import GS.Core

@[expose] public section


/-! Perfect shuffle, expressed using pair coordinates before flattening.
The pair (r,s) is the manuscript's scalar coordinate r*b+s.
 -/

noncomputable section
namespace GS

/-- Explicit block-diagonal embedding, useful also for shared blocks. -/
def blockMatrix {R : Type*} [Zero R] {k b : ℕ} (B : Fin k → Matrix (Fin b) (Fin b) R) :
    Matrix (Fin k × Fin b) (Fin k × Fin b) R :=
  fun i j => if i.1 = j.1 then B i.1 i.2 j.2 else 0

end GS
