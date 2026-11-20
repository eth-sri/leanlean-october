module

public import ADR11.Computation.Program
meta import ADR11.Computation.Program

/-! Five crossing gene trees on the standard unrooted skeleton, one for
    each choice of the middle leaf. None contains either cherry of the skeleton. -/
@[expose] public section
namespace ADR11.Skeleton
open Finset _root_.ADR11.Computation Real

def crossing (i : Fin 5) :=
  let (a,b) := (![(10,11),(9,11),(9,13),(5,13),(5,21)] : Fin 5 → ℕ × ℕ) i
  unroot (decF 5 [1,2,4,8,16,a,b,31])

/-- Each possible cut contributes a contrast between probes inside and outside it. -/
def cuts := [7,28,15,23,27,29,30]
def codes := [3,24] ++ cuts
abbrev shapes := catalogue 5 codes

abbrev triple (c : ℕ) := c = 7 ∨ c = 28
def middle (c : ℕ) := if triple c then 2 else 1
def width (c : ℕ) := if triple c then 2 else 6
def factor (c : ℕ) := if triple c then 3 else 1
def outside (c : ℕ) (i : Fin 5) : ℤ := if c.testBit i then 0 else 1
def tilt (i : Fin 5) (c : ℕ) : ℤ := 5 * outside c i - middle c

def baseKey : Sparse.Key := {3,28,24,7}
def stageKey (c : ℕ) := if triple c then baseKey else baseKey + 2 • ({7,28} : Sparse.Key)
def terms (i : Fin 5) (c : ℕ) : Sparse.Poly :=
  let q : ℚ := tilt i c * factor c / 90
  {(q,stageKey c), (-q,stageKey c + Multiset.replicate (width c) c)}
def polynomial (i : Fin 5) : Sparse.Poly :=
  (1/15,baseKey) ::ₘ (∑ c ∈ cuts.toFinset, terms i c)

set_option maxHeartbeats 4000000 in
theorem checked : ∀ s ∈ shapes, ∀ i, Sparse.verifies s (crossing i) (polynomial i) = true := by check_forms 5 codes

end ADR11.Skeleton
