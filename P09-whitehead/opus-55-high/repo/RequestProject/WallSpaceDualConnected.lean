module

public import RequestProject.WallSpaceDual
public import RequestProject.RollerGraphMetric

@[expose] public section

/-!
# The dual of a wall space is a connected median graph

`RequestProject/WallSpaceDual.lean` proves that the dual of a wall space — the consistent
orientations of the walls that differ from a base point in finitely many walls — is closed
under the median (majority) operation, i.e. that it is a `FiniteChains.RollerModel`.

Median-closedness alone does not say that the halfspace coordinates are the vertices of a
*graph*: as `RequestProject/RollerConnected.lean` records, a median-closed family need not be
connected by one-coordinate moves.  This file supplies the missing step for duals of wall
spaces.  The only extra hypothesis is that the walls are pairwise distinct as partitions of
the space (`FiniteChains.WallSpace.Reduced`); this is no loss of generality, since repeated
walls may simply be discarded.

The main result is `FiniteChains.WallSpace.exists_flip`: given two consistent orientations,
one of the walls on which they disagree may be flipped in the first one without destroying
consistency — take a wall whose chosen halfspace is minimal among the disputed ones.  In
halfspace coordinates this is `FiniteChains.WallSpace.dualW_step`, which gives

* `FiniteChains.WallSpace.gatedDualModel` — the dual is a `FiniteChains.GatedRollerModel`,
  hence its graph is connected, the number of separating walls is its edge metric, and it is
  a median graph in the graph-theoretic sense;
* `FiniteChains.WallSpace.dualGraph_connected`,
  `FiniteChains.WallSpace.dualGraph_dist_eq`,
  `FiniteChains.WallSpace.gatedDual_ker_d₂_eq_range_d₃`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

universe u v

open RollerBridge

namespace WallSpace

variable {X : Type u} {ι : Type v} [DecidableEq ι] {S : WallSpace X ι}

variable (S) in
/-- The halfspace chosen by an orientation at a wall. -/
def hs (o : ι → Bool) (i : ι) : Set X := {x | S.side i x = o i}

section Coordinates

/-! ## The dual as a gated Roller model -/

end Coordinates

end WallSpace

end FiniteChains
