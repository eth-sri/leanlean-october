/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleDualCarrier
public import PottsDiscontinuity.Duality.SignedFlowDimension

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

noncomputable section

section
variable (a : LatticeVertex) (w h : ℕ)
/-- The normalized bond underlying a genuine induced-rectangle edge has its
actual endpoints in the rectangle. -/
theorem rectanglePrimalEdgeBond_endpoints_mem_public
    (e : rectanglePrimalEdgeCarrier a w h) :
    (rectanglePrimalEdgeBond a w h e).source ∈ latticeRectangle a w h ∧
      (rectanglePrimalEdgeBond a w h e).target ∈ latticeRectangle a w h := by
  let p := e.1.out
  have hrepr : s(p.1, p.2) = e.1 := Quot.out_eq _
  have hbondEdge :=
    Equiv.apply_symm_apply wholePlaneBondEdgeEquiv
      (rectanglePrimalEdgeToSquareEdge a w h e)
  have hbondSym2 : (rectanglePrimalEdgeBond a w h e).toSym2 =
      Sym2.map (fun z : RectangleVertex a w h => z.val) e.1 := by
    have hh := congrArg Subtype.val hbondEdge
    tauto
  have hm : Sym2.map (fun z : RectangleVertex a w h => z.val) e.1 =
      s(p.1.val, p.2.val) := by
    rw [← hrepr]
    rfl
  grind [rectanglePrimalEdgeBond, LatticeBond.toSym2]

/-- The public unordered-edge identity underlying the normalized rectangle bond. -/
theorem rectanglePrimalEdgeBond_toSym2_public
    (e : rectanglePrimalEdgeCarrier a w h) :
    (rectanglePrimalEdgeBond a w h e).toSym2 =
      Sym2.map (fun z : RectangleVertex a w h => z.val) e.1 := by
  have hbondEdge :=
    Equiv.apply_symm_apply wholePlaneBondEdgeEquiv
      (rectanglePrimalEdgeToSquareEdge a w h e)
  have hh := congrArg Subtype.val hbondEdge
  tauto

/-- An in-rectangle normalized bond determines an actual edge of the induced
rectangle graph through its two genuine endpoint vertices. -/
def rectanglePrimalBondToEdge (b : RectanglePrimalBond a w h) : rectanglePrimalEdgeCarrier a w h := by
  let u : RectangleVertex a w h := ⟨b.1.source, b.2.1⟩
  let v : RectangleVertex a w h := ⟨b.1.target, b.2.2⟩
  refine ⟨s(u, v), ?_⟩
  exact (rectangleGraph_adj_iff a w h u v).2 b.1.adjacent

/-- Every edge of the induced rectangle graph is exactly one normalized
right/up bond with both endpoints in the rectangle. -/
noncomputable def rectanglePrimalEdgeBondEquiv  :
    rectanglePrimalEdgeCarrier a w h ≃ RectanglePrimalBond a w h where
  toFun e := ⟨rectanglePrimalEdgeBond a w h e,
    rectanglePrimalEdgeBond_endpoints_mem_public a w h e⟩
  invFun := rectanglePrimalBondToEdge a w h
  left_inv e := by
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    let b := rectanglePrimalEdgeBond a w h e
    have hbond := rectanglePrimalEdgeBond_toSym2_public a w h e
    tauto
  right_inv b := by
    apply Subtype.ext
    apply LatticeBond.toSym2_injective
    have heq := rectanglePrimalEdgeBond_toSym2_public a w h
      (rectanglePrimalBondToEdge a w h b)
    tauto

/-- Orient every selected open edge by its normalized lattice bond, not by an
arbitrary representative of its unordered pair. -/
def rectangleOpenEdgeOrientation (A : Configuration (rectangleGraph a w h)) :
    SignedFlowOrientation (rectangleGraph a w h) A where
  source e := ⟨(rectanglePrimalEdgeBond a w h e.1).source,
    (rectanglePrimalEdgeBond_endpoints_mem_public a w h e.1).1⟩
  target e := ⟨(rectanglePrimalEdgeBond a w h e.1).target,
    (rectanglePrimalEdgeBond_endpoints_mem_public a w h e.1).2⟩
  endpoints e := by
    apply Sym2.map.injective Subtype.val_injective
    simpa [LatticeBond.toSym2] using
      rectanglePrimalEdgeBond_toSym2_public a w h e.1

/-- The signed-flow nullity identity on the actual rectangle graph, retaining
all rectangle vertices, including isolated ones and degenerate rectangles. -/
theorem rectangleSignedFlowDimension (A : Configuration (rectangleGraph a w h)) :
    Module.finrank ℝ (LinearMap.ker
      (signedDivergence (rectangleGraph a w h) A
        (rectangleOpenEdgeOrientation a w h A))) +
        Fintype.card (RectangleVertex a w h) =
      A.card + componentCount (rectangleGraph a w h)
        (BoundaryCondition.free (∅ : Set (RectangleVertex a w h))) A :=
  signedFlowDimension (rectangleGraph a w h) A (rectangleOpenEdgeOrientation a w h A)
end

end
end PottsDiscontinuity.FK
