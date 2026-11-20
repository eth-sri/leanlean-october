module

public import Mathlib

/-!
# The local free-fermion identity

Slater determinants diagonalize simultaneous independent left/right moves on
integer lifts. These are identities on the full lifted carrier. Turning them into
an eigenvector on the cyclic defect states also requires the seam/twist and
positivity arguments; no such finite-state conclusion is assumed here.
-/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {k : ℕ} (z : Fin k → ℂ) (x : Fin k → ℤ)

include z x in
/-- The plane-wave matrix, with positions indexing rows and momenta indexing columns. -/
noncomputable def planeWaveMatrix : Matrix (Fin k) (Fin k) ℂ :=
  fun b a => z a ^ x b

include z x in
/-- A Slater determinant evaluated on integer lifts. -/
noncomputable def slater : ℂ := (planeWaveMatrix z x).det

/-- Consecutive, centered momenta. For `q = exp(iπ/L)` these are the momenta
`π(2a+1-k)/L`, with the antiperiodic twist when `k` is even. -/
noncomputable def centeredMomenta (q : ℂ) : Fin k → ℂ :=
  fun a => q ^ (2 * (a.val : ℤ) + 1 - (k : ℤ))

end PottsDiscontinuity.SixVertex
