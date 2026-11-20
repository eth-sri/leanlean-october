module

public import PottsDiscontinuity.FK.FiniteEnergy

/-!
# Finite-energy lower bounds for closed edge sets

The FK single-edge finite-energy estimate iterates to a uniform lower bound
for every prescribed finite set of edges to be closed. In particular, four
specified edges have closed probability at least `(1 - p)^4`.
-/

@[expose] public section

namespace PottsDiscontinuity.Potts

open MeasureTheory

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

/-- Configurations in which every edge in `F` is closed. -/
def allClosedEdges (F : Finset G.edgeSet) : Set (FK.Configuration G) :=
  {A | Disjoint F A}

/-- In any finite FK measure, each prescribed finite set of edges is closed
with probability at least `(1-p)` to the power of its cardinality. -/
theorem measure_allClosedEdges_lower_bound (q : FK.Parameters)
    (ξ : FK.BoundaryCondition V) (F : Finset G.edgeSet) :
    (1 - FK.edgeParameter q) ^ F.card ≤
      (FK.measure G q ξ (allClosedEdges F)).toReal := by
  simpa only [allClosedEdges, Finset.disjoint_left, Bool.false_eq_true, iff_false, ↓reduceIte] using
    FK.measure_prescribed_edges_lower_bound q ξ false F

end

end PottsDiscontinuity.Potts
