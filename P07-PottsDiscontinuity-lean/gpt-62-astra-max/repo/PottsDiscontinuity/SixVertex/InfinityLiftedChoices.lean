module

public import PottsDiscontinuity.SixVertex.InfinityChoices
public import PottsDiscontinuity.SixVertex.InfinityMoves
public import PottsDiscontinuity.SixVertex.InfinitySupport
public import PottsDiscontinuity.SixVertex.InfinityPhase

/-! # Indexed choices and collision cancellation on shifted lifts -/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ}

/-- Read indexed choices on the canonical ordered defect sites. -/
noncomputable def indexedDefectChoice {x : Finset (Fin N)}
    (d : Fin (defects x).card → Bool) : DefectChoice x :=
  fun i => d ((defects x).orderIsoOfFin rfl |>.symm i)

variable {k : ℕ} (L : ℝ) (x : Fin k → ℤ) {a b : Fin k} (hab : a ≠ b) {s : Finset (Fin N)}
    (hs : s.card = k)

end PottsDiscontinuity.SixVertex
