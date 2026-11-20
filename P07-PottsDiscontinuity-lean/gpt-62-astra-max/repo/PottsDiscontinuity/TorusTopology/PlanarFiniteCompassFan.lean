/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Factored finite table proof to avoid repeated cardinal computations; namespace/import relocation; antipodal turn is the principal value +2, agreeing with the original on every nonbacktracking pair. -/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

variable (Q : Finset (Fin 4)) (a b : Fin 4)

include Q in
/-- For a set of compass sectors, the signed boundary at direction `d` is its
indicator minus the indicator of the preceding sector. Directions are the
cyclic compass labels `0 = E, 1 = N, 2 = W, 3 = S`. -/
def compassSectorBoundary (d : Fin 4) : ℤ :=
  (if d ∈ Q then 1 else 0) - (if d - 1 ∈ Q then 1 else 0)

include a b in
/-- The signed quarter-turn for travel directions. The input directions are
those of travel; the antipodal case uses the principal value +2.
Nonbacktracking circuits exclude that case. -/
def primalCompassQuarterTurn : ℤ :=
  if b = a + 1 then 1 else if b = a + 3 then -1 else if b = a + 2 then 2 else 0

end PottsDiscontinuity.TorusTopology.Planar.Medial
