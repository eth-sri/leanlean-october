/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleFlowDimension
public import Mathlib.Data.Int.Interval

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

noncomputable section

section
variable (a : LatticeVertex) (w h : ℕ)
/-- The ordinary induced square-lattice graph on the expanded dual vertex box. -/
def rectangleDualAmbientGraph  :
    SimpleGraph (RectangleDualVertex a w h) :=
  squareLattice.induce (rectangleDualExpanded a w h : Set LatticeVertex)

theorem rectangleDualAmbientGraph_adj_iff (u v : RectangleDualVertex a w h) :
    (rectangleDualAmbientGraph a w h).Adj u v ↔ squareLattice.Adj u.1 v.1 := by
  rfl

theorem primalBondOfDual_endpoints_mem_of_interior_endpoint
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
      simp only [LatticeBond.source, LatticeBond.target,
        primalBondOfDual, LatticeBond.source, LatticeBond.target] at hcoord ⊢ <;>
      simp only [mem_latticeRectangle] at hcoord ⊢ <;>
      omega
  · subst z
    rcases d with ⟨base, axis⟩
    cases axis <;>
      simp only [LatticeBond.source, LatticeBond.target,
        primalBondOfDual, LatticeBond.source, LatticeBond.target] at hcoord ⊢ <;>
      simp only [mem_latticeRectangle] at hcoord ⊢ <;>
      omega

theorem rectangleDualAmbient_adj_actual_of_left_interior
    (u v : RectangleDualVertex a w h)
    (hu : u.1 ∈ rectangleDualInterior a w h)
    (hadj : (rectangleDualAmbientGraph a w h).Adj u v) :
    (rectangleDualGraph a w h).Adj u v := by
  obtain ⟨d, hd⟩ := LatticeBond.exists_of_adj (by tauto)
  have hpairSource : s(d.source, d.target) = s(u.1, v.1) := by
    tauto
  have hzu : u.1 = d.source ∨ u.1 = d.target := by
    grind
  let b : RectanglePrimalBond a w h := ⟨primalBondOfDual d, (primalBondOfDual_endpoints_mem_of_interior_endpoint a w h d u.1 hu hzu)⟩
  let pe := rectanglePrimalBondToEdge a w h b
  let de := rectanglePrimalDualEdgeEquiv a w h pe
  have hpe : rectanglePrimalEdgeBond a w h pe = primalBondOfDual d :=
    congrArg Subtype.val ((rectanglePrimalEdgeBondEquiv a w h).right_inv b)
  have hcross : de.crossingBond = d := by
    change rectangleCrossingDualBond a w h pe = d
    simp_all [rectangleCrossingDualBond]
  have hpairCarrier : rectangleDualCarrierPair a w h de = s(u, v) := by
    apply Sym2.map.injective Subtype.val_injective
    calc
      Sym2.map Subtype.val (rectangleDualCarrierPair a w h de) = de.crossingBond.toSym2 := by
        rfl
      _ = d.toSym2 := congrArg LatticeBond.toSym2 hcross
      _ = s(u.1, v.1) := hd
  exact (rectangleDualGraph_adj_iff a w h u v).2 ⟨de, hpairCarrier.symm⟩

theorem rectangleDualGraph_le_ambient  :
    rectangleDualGraph a w h ≤ rectangleDualAmbientGraph a w h := by
  intro u v hadj
  rw [rectangleDualAmbientGraph_adj_iff]
  obtain ⟨e, he⟩ := (rectangleDualGraph_adj_iff a w h u v).mp hadj
  have hpair := congrArg (Sym2.map (fun z : RectangleDualVertex a w h => z.1)) he
  have hpair' : s(u.1, v.1) = s(e.crossingBond.source, e.crossingBond.target) := by
    tauto
  rcases Sym2.eq_iff.mp hpair' with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [hs, ht]
    exact e.crossingBond.adjacent
  · rw [hs, ht]
    exact e.crossingBond.adjacent.symm

theorem rectangleDualAmbient_extraEdge_endpoints_boundary
    (u v : RectangleDualVertex a w h)
    (hadj : (rectangleDualAmbientGraph a w h).Adj u v)
    (hnot : ¬ (rectangleDualGraph a w h).Adj u v) :
    u.1 ∈ rectangleDualBoundary a w h ∧ v.1 ∈ rectangleDualBoundary a w h := by
  have hu : u.1 ∈ rectangleDualBoundary a w h := by
    by_contra hU
    have hui : u.1 ∈ rectangleDualInterior a w h := by
      by_contra hInterior
      exact hU (Finset.mem_filter.mpr ⟨u.2, hInterior⟩)
    grind [hnot, rectangleDualAmbient_adj_actual_of_left_interior]
  have hv : v.1 ∈ rectangleDualBoundary a w h := by
    by_contra hV
    have hvi : v.1 ∈ rectangleDualInterior a w h := by
      by_contra hInterior
      exact hV (Finset.mem_filter.mpr ⟨v.2, hInterior⟩)
    have hrev := rectangleDualAmbient_adj_actual_of_left_interior a w h v u hvi hadj.symm
    exact hnot hrev.symm
  simp_all
end

end

end PottsDiscontinuity.FK
