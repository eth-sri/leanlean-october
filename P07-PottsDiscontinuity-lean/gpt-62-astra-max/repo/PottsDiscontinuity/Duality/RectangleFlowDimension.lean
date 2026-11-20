/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleDualCarrier
public import PottsDiscontinuity.Duality.SignedFlowDimension

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

noncomputable section

variable {a : LatticeVertex} {w h : ℕ} (e : rectanglePrimalEdgeCarrier a w h)

/-- The normalized bond underlying a genuine induced-rectangle edge has its
actual endpoints in the rectangle. -/
theorem rectanglePrimalEdgeBond_endpoints_mem_public :
    (rectanglePrimalEdgeBond e).source ∈ latticeRectangle a w h ∧
      (rectanglePrimalEdgeBond e).target ∈ latticeRectangle a w h := by
  let p := e.1.out
  have hrepr : s(p.1, p.2) = e.1 := Quot.out_eq _
  have hbondEdge :=
    Equiv.apply_symm_apply wholePlaneBondEdgeEquiv
      (rectanglePrimalEdgeToSquareEdge e)
  have hbondSym2 : (rectanglePrimalEdgeBond e).toSym2 =
      Sym2.map (fun z : RectangleVertex a w h => z.val) e.1 := by
    have hh := congrArg Subtype.val hbondEdge
    exact hh
  have hm : Sym2.map (fun z : RectangleVertex a w h => z.val) e.1 =
      s(p.1.val, p.2.val) := by
    rw [← hrepr]
    rfl
  have heq : s((rectanglePrimalEdgeBond e).source,
      (rectanglePrimalEdgeBond e).target) = s(p.1.val, p.2.val) := by
    simpa [LatticeBond.toSym2] using hbondSym2.trans hm
  grind

/-- The public unordered-edge identity underlying the normalized rectangle bond. -/
theorem rectanglePrimalEdgeBond_toSym2_public :
    (rectanglePrimalEdgeBond e).toSym2 =
      Sym2.map (fun z : RectangleVertex a w h => z.val) e.1 := by
  have hbondEdge :=
    Equiv.apply_symm_apply wholePlaneBondEdgeEquiv
      (rectanglePrimalEdgeToSquareEdge e)
  have hh := congrArg Subtype.val hbondEdge
  exact hh

/-- An in-rectangle normalized bond determines an actual edge of the induced
rectangle graph through its two genuine endpoint vertices. -/
def rectanglePrimalBondToEdge
    (b : RectanglePrimalBond a w h) : rectanglePrimalEdgeCarrier a w h := by
  let u : RectangleVertex a w h := ⟨b.1.source, b.2.1⟩
  let v : RectangleVertex a w h := ⟨b.1.target, b.2.2⟩
  refine ⟨s(u, v), ?_⟩
  exact (rectangleGraph_adj_iff a w h u v).2 b.1.adjacent

/-- Every edge of the induced rectangle graph is exactly one normalized
right/up bond with both endpoints in the rectangle. -/
noncomputable def rectanglePrimalEdgeBondEquiv (a : LatticeVertex) (w h : ℕ) :
    rectanglePrimalEdgeCarrier a w h ≃ RectanglePrimalBond a w h where
  toFun e := ⟨rectanglePrimalEdgeBond e,
    rectanglePrimalEdgeBond_endpoints_mem_public e⟩
  invFun := rectanglePrimalBondToEdge (a := a) (w := w) (h := h)
  left_inv e := by
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    let b := rectanglePrimalEdgeBond e
    have hbond := rectanglePrimalEdgeBond_toSym2_public e
    change Sym2.map (fun z : RectangleVertex a w h => z.val)
        (s(⟨b.source, (rectanglePrimalEdgeBond_endpoints_mem_public e).1⟩,
           ⟨b.target, (rectanglePrimalEdgeBond_endpoints_mem_public e).2⟩)) = _
    simpa [b, LatticeBond.toSym2] using hbond
  right_inv b := by
    apply Subtype.ext
    apply LatticeBond.toSym2_injective
    have heq := rectanglePrimalEdgeBond_toSym2_public
      (rectanglePrimalBondToEdge b)
    change (rectanglePrimalEdgeBond (rectanglePrimalBondToEdge b)).toSym2 =
      b.1.toSym2 at heq
    exact heq

/-- Orient every selected open edge by its normalized lattice bond, not by an
arbitrary representative of its unordered pair. -/
def rectangleOpenEdgeOrientation
    (A : Configuration (rectangleGraph a w h)) :
    SignedFlowOrientation (rectangleGraph a w h) A where
  source e := ⟨(rectanglePrimalEdgeBond e.1).source,
    (rectanglePrimalEdgeBond_endpoints_mem_public e.1).1⟩
  target e := ⟨(rectanglePrimalEdgeBond e.1).target,
    (rectanglePrimalEdgeBond_endpoints_mem_public e.1).2⟩
  endpoints e := by
    apply Sym2.map.injective Subtype.val_injective
    simpa [LatticeBond.toSym2] using
      rectanglePrimalEdgeBond_toSym2_public e.1

/-- The signed-flow nullity identity on the actual rectangle graph, retaining
all rectangle vertices, including isolated ones and degenerate rectangles. -/
theorem rectangleSignedFlowDimension (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    Module.finrank ℝ (LinearMap.ker
      (signedDivergence (rectangleGraph a w h) A
        (rectangleOpenEdgeOrientation A))) +
        Fintype.card (RectangleVertex a w h) =
      A.card + componentCount
        (BoundaryCondition.free (∅ : Set (RectangleVertex a w h))) A :=
  signedFlowDimension (rectangleGraph a w h) A (rectangleOpenEdgeOrientation A)

end
end PottsDiscontinuity.FK
