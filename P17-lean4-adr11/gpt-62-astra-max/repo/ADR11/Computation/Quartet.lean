module
public import ADR11.Computation.Program
meta import ADR11.Computation.Program
@[expose] public section
namespace ADR11.Quartet
open Finset Skeleton _root_.ADR11.Computation
abbrev Tree := SpeciesTree (Fin 4)

def side (i : Fin 3) : ℕ := ![3,5,6] i
def key (i : Fin 3) : Sparse.Key := {side i,15-side i}
def pairs := key 0 + key 1 + key 2
def gene (i : Fin 3) := unroot (decF 4 [1,2,4,8,side i,15])
def polynomial (i : Fin 3) : Sparse.Poly :=
  {(1,0), (-1,key i), (1/3,pairs)}

set_option maxHeartbeats 3000000 in
theorem checked : ∀ s ∈ full 4, ∀ i, Sparse.verifies s (gene i) (polynomial i) = true := by check_forms 4 (inner 4)

end ADR11.Quartet
