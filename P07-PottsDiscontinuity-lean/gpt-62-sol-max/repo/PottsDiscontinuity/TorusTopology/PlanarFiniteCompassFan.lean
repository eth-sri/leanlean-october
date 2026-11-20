/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Factored finite table proof to avoid repeated cardinal computations; namespace/import relocation; antipodal turn is the principal value +2, agreeing with the original on every nonbacktracking pair. -/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

/-- The signed quarter-turn for travel directions. The input directions are
those of travel; the antipodal case uses the principal value +2.
Nonbacktracking circuits exclude that case. -/
def primalCompassQuarterTurn (a b : Fin 4) : ℤ :=
  if b = a + 1 then 1 else if b = a + 3 then -1 else if b = a + 2 then 2 else 0

end PottsDiscontinuity.TorusTopology.Planar.Medial
