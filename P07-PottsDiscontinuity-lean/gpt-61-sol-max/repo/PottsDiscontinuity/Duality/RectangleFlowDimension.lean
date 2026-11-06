/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

public import PottsDiscontinuity.Duality.RectangleDualCarrier
public import PottsDiscontinuity.Duality.SignedFlowDimension

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

noncomputable section

section

variable (a : LatticeVertex) (w h : ℕ) (e : rectanglePrimalEdgeCarrier a w h)
include e

/-- The normalized bond underlying a genuine induced-rectangle edge has its
actual endpoints in the rectangle. -/
theorem rectanglePrimalEdgeBond_endpoints_mem_public
     :
    (rectanglePrimalEdgeBond a w h e).source ∈ latticeRectangle a w h ∧
      (rectanglePrimalEdgeBond a w h e).target ∈ latticeRectangle a w h := by
  let p := e.1.out
  have hrepr : s(p.1, p.2) = e.1 := Quot.out_eq _
  
  have hbondSym2 : (rectanglePrimalEdgeBond a w h e).toSym2 =
      Sym2.map (fun z : RectangleVertex a w h => z.val) e.1 := congrArg Subtype.val (Equiv.apply_symm_apply wholePlaneBondEdgeEquiv
                                                                                         (rectanglePrimalEdgeToSquareEdge a w h e))
  have hm : Sym2.map (fun z  => z.val) e.1 =
      s(p.1.val, p.2.val) := by
    rw [← hrepr]
    rfl
  have heq : s((rectanglePrimalEdgeBond a w h e).source,
      (rectanglePrimalEdgeBond a w h e).target) = s(p.1.val, p.2.val) := by
    simp_all [LatticeBond.toSym2]
  rcases Sym2.eq_iff.mp heq with ⟨hs, ht⟩ | ⟨hs, ht⟩
  all_goals simp_all

/-- The public unordered-edge identity underlying the normalized rectangle bond. -/
theorem rectanglePrimalEdgeBond_toSym2_public
     :
    (rectanglePrimalEdgeBond a w h e).toSym2 =
      Sym2.map (fun z : RectangleVertex a w h => z.val) e.1 := congrArg Subtype.val (Equiv.apply_symm_apply wholePlaneBondEdgeEquiv (rectanglePrimalEdgeToSquareEdge a w h e))

end

/-- An in-rectangle normalized bond determines an actual edge of the induced
rectangle graph through its two genuine endpoint vertices. -/
def rectanglePrimalBondToEdge (a : LatticeVertex) (w h : ℕ)
    (b : RectanglePrimalBond a w h) : rectanglePrimalEdgeCarrier a w h := ⟨s( ⟨b.1.source, b.2.1⟩ ,  ⟨b.1.target, b.2.2⟩ ), (rectangleGraph_adj_iff a w h  ⟨b.1.source, b.2.1⟩   ⟨b.1.target, b.2.2⟩ ).2 b.1.adjacent⟩

/-- Every edge of the induced rectangle graph is exactly one normalized
right/up bond with both endpoints in the rectangle. -/
noncomputable def rectanglePrimalEdgeBondEquiv (a : LatticeVertex) (w h : ℕ) :
    rectanglePrimalEdgeCarrier a w h ≃ RectanglePrimalBond a w h where
  toFun e := ⟨rectanglePrimalEdgeBond a w h e,
    rectanglePrimalEdgeBond_endpoints_mem_public a w h e⟩
  invFun := rectanglePrimalBondToEdge a w h
  left_inv e := Subtype.ext (Sym2.map.injective Subtype.val_injective (rectanglePrimalEdgeBond_toSym2_public a w h e))
  right_inv b := Subtype.ext
                   (LatticeBond.toSym2_injective (rectanglePrimalEdgeBond_toSym2_public a w h (rectanglePrimalBondToEdge a w h b)))

/-- Orient every selected open edge by its normalized lattice bond, not by an
arbitrary representative of its unordered pair. -/
def rectangleOpenEdgeOrientation (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    SignedFlowOrientation (rectangleGraph a w h) A where
  source e := ⟨(rectanglePrimalEdgeBond a w h e.1).source,
    (rectanglePrimalEdgeBond_endpoints_mem_public a w h e.1).1⟩
  target e := ⟨(rectanglePrimalEdgeBond a w h e.1).target,
    (rectanglePrimalEdgeBond_endpoints_mem_public a w h e.1).2⟩
  endpoints e := by
    apply Sym2.map.injective Subtype.val_injective
    exact
      rectanglePrimalEdgeBond_toSym2_public a w h e.1

/-- The signed-flow nullity identity on the actual rectangle graph, retaining
all rectangle vertices, including isolated ones and degenerate rectangles. -/
theorem rectangleSignedFlowDimension (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    Module.finrank ℝ (LinearMap.ker
      (signedDivergence (rectangleGraph a w h) A
        (rectangleOpenEdgeOrientation a w h A))) +
        Fintype.card (RectangleVertex a w h) =
      A.card + componentCount (rectangleGraph a w h)
        (BoundaryCondition.free (∅ : Set (RectangleVertex a w h))) A :=
  by
    solve_by_elim [_root_.PottsDiscontinuity.FK.signedFlowDimension]

end
end PottsDiscontinuity.FK
