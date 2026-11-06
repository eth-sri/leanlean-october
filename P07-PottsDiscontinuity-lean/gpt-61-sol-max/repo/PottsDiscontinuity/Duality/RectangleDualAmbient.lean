/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

public import PottsDiscontinuity.Duality.RectangleFlowDimension
public import Mathlib.Data.Int.Interval

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

noncomputable section

/-- The ordinary induced square-lattice graph on the expanded dual vertex box. -/
def rectangleDualAmbientGraph (a : LatticeVertex) (w h : ℕ) :
    SimpleGraph (RectangleDualVertex a w h) :=
  squareLattice.induce (rectangleDualExpanded a w h : Set LatticeVertex)

section

variable (a : LatticeVertex) (w h : ℕ)


theorem rectangleDualAmbientGraph_adj_iff 
    (u v : RectangleDualVertex a w h) :
    (rectangleDualAmbientGraph a w h).Adj u v ↔ squareLattice.Adj u.1 v.1 := by
  simp [rectangleDualAmbientGraph]

private theorem primalBondOfDual_endpoints_mem_of_interior_endpoint
     (d : LatticeBond) (z : LatticeVertex)
    (hz : z ∈ rectangleDualInterior a w h)
    (hzd : z = d.source ∨ z = d.target) :
    (primalBondOfDual d).source ∈ latticeRectangle a w h ∧
      (primalBondOfDual d).target ∈ latticeRectangle a w h := by
  have hcoord := (Finset.mem_filter.mp hz).2
  rcases hzd with h | h
  · subst z
    rcases d with ⟨base, axis⟩
    cases axis <;>
      simp only [LatticeBond.source, LatticeBond.target, primalBondOfDual] at hcoord ⊢ <;>
      simp only [mem_latticeRectangle] at hcoord ⊢ <;>
      omega
  · subst z
    rcases d with ⟨base, axis⟩
    cases axis <;>
      simp only [LatticeBond.source, LatticeBond.target, primalBondOfDual] at hcoord ⊢ <;>
      simp only [mem_latticeRectangle] at hcoord ⊢ <;>
      omega

theorem rectangleDualAmbient_adj_actual_of_left_interior
     (u v : RectangleDualVertex a w h)
    (hu : u.1 ∈ rectangleDualInterior a w h)
    (hadj : (rectangleDualAmbientGraph a w h).Adj u v) :
    (rectangleDualGraph a w h).Adj u v := by
  
  obtain ⟨d, hd⟩ := LatticeBond.exists_of_adj ((rectangleDualAmbientGraph_adj_iff a w h u v).mp hadj)
  have hpairSource : s(d.source, d.target) = s(u.1, v.1) := by
    simpa [LatticeBond.toSym2] using hd
  
  
  let b : RectanglePrimalBond a w h := ⟨primalBondOfDual d,  primalBondOfDual_endpoints_mem_of_interior_endpoint a w h d u.1 hu (by
                                                                                                                                              grind) ⟩
  let pe  := rectanglePrimalBondToEdge a w h b
  let de  := rectanglePrimalDualEdgeEquiv a w h pe
  have hpe : rectanglePrimalEdgeBond a w h pe = primalBondOfDual d := congrArg Subtype.val ((rectanglePrimalEdgeBondEquiv a w h).right_inv b)
  
  
  exact (rectangleDualGraph_adj_iff a w h u v).2 ⟨de, (Sym2.map.injective Subtype.val_injective
                                                                                                                            (Trans.trans
                                                                                                                              (Trans.trans (of_eq_true (eq_self s(de.crossingBond.source, de.crossingBond.target)))
                                                                                                                                (congrArg LatticeBond.toSym2 (by
                                                                                                                                                                change rectangleCrossingDualBond a w h pe = d
                                                                                                                                                                rw [rectangleCrossingDualBond, hpe]
                                                                                                                                                                exact dualBondOfPrimal_primalBondOfDual d)))
                                                                                                                              hd)).symm⟩

theorem rectangleDualGraph_le_ambient  :
    rectangleDualGraph a w h ≤ rectangleDualAmbientGraph a w h := by
  intro u v hadj
  rw [rectangleDualAmbientGraph_adj_iff]
  obtain ⟨e, he⟩ := (rectangleDualGraph_adj_iff a w h u v).mp hadj
  have hpair := congrArg (Sym2.map  fun z  => z.1 ) he
  have hpair' : s(u.1, v.1) = s(e.crossingBond.source, e.crossingBond.target) := by
    assumption
  rcases Sym2.eq_iff.mp hpair' with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [hs, ht]
    exact e.crossingBond.adjacent
  · rw [hs, ht]
    exact e.crossingBond.adjacent.symm

theorem rectangleDualAmbient_extraEdge_endpoints_boundary
     (u v : RectangleDualVertex a w h)
    (hadj : (rectangleDualAmbientGraph a w h).Adj u v)
    (hnot : ¬ (rectangleDualGraph a w h).Adj u v) :
    u.1 ∈ rectangleDualBoundary a w h ∧ v.1 ∈ rectangleDualBoundary a w h := ⟨Decidable.byContradiction fun hU =>
                                                                                 hnot
                                                                                   (rectangleDualAmbient_adj_actual_of_left_interior a w h u v
                                                                                     (Decidable.byContradiction fun hInterior => hU (Finset.mem_filter.mpr ⟨u.property, hInterior⟩)) hadj),
                                                                               Decidable.byContradiction fun hV =>
                                                                                 hnot
                                                                                   (SimpleGraph.Adj.symm
                                                                                     (rectangleDualAmbient_adj_actual_of_left_interior a w h v u
                                                                                       (Decidable.byContradiction fun hInterior => hV (Finset.mem_filter.mpr ⟨v.property, hInterior⟩))
                                                                                       (SimpleGraph.Adj.symm hadj)))⟩

end

end

end PottsDiscontinuity.FK
