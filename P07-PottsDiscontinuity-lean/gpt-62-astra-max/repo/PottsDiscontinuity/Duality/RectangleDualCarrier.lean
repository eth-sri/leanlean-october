/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.Rectangle
public import PottsDiscontinuity.Duality.WholePlaneDualConfiguration
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

noncomputable section

/-- The expanded face-base rectangle `[-1,w] × [-1,h]` relative to `a`. -/
def rectangleDualExpanded (a : LatticeVertex) (w h : ℕ) : Finset LatticeVertex :=
  latticeRectangle (a.1 - 1, a.2 - 1) (w + 1) (h + 1)

/-- Integer face bases strictly inside the rectangle. For a zero side length
this set is empty, as required. -/
def rectangleDualInterior (a : LatticeVertex) (w h : ℕ) : Finset LatticeVertex :=
  (rectangleDualExpanded a w h).filter fun z =>
    a.1 ≤ z.1 ∧ z.1 < a.1 + w ∧
    a.2 ≤ z.2 ∧ z.2 < a.2 + h

/-- Every expanded dual vertex not strictly internal is part of the wired
boundary/exterior class, including isolated corners and degenerate boxes. -/
def rectangleDualBoundary (a : LatticeVertex) (w h : ℕ) : Finset LatticeVertex :=
  (rectangleDualExpanded a w h).filter fun z => z ∉ rectangleDualInterior a w h

/-- A normalized original bond whose two endpoints lie in the primal rectangle. -/
abbrev RectanglePrimalBond (a : LatticeVertex) (w h : ℕ) :=
  {b : LatticeBond // b.source ∈ latticeRectangle a w h ∧
    b.target ∈ latticeRectangle a w h}

/-- The finite carrier of original primal edges in the rectangle. -/
def rectanglePrimalEdgeCarrier (a : LatticeVertex) (w h : ℕ) :=
  (rectangleGraph a w h).edgeSet

/-- Embed an actual induced-rectangle edge into the whole-plane edge carrier. -/
noncomputable def rectanglePrimalEdgeToSquareEdge {a : LatticeVertex} {w h : ℕ}
    (e : rectanglePrimalEdgeCarrier a w h) : squareLattice.edgeSet := by
  let p := e.1.out
  have hrepr : s(p.1, p.2) = e.1 := Quot.out_eq _
  have hsq :=
    (rectangleGraph_adj_iff a w h p.1 p.2).mp (by
      have hm : s(p.1, p.2) ∈ (rectangleGraph a w h).edgeSet := by
        rw [hrepr]
        exact e.2
      exact hm)
  refine ⟨Sym2.map (fun z : RectangleVertex a w h => z.val) e.1, ?_⟩
  have heq : Sym2.map (fun z : RectangleVertex a w h => z.val) e.1 =
      s(p.1.val, p.2.val) := by
    rw [← hrepr]
    rfl
  simp_all

noncomputable def rectanglePrimalEdgeBond {a : LatticeVertex} {w h : ℕ}
    (e : rectanglePrimalEdgeCarrier a w h) : LatticeBond :=
  wholePlaneBondEdgeEquiv.symm (rectanglePrimalEdgeToSquareEdge e)

private theorem rectanglePrimalEdgeBond_edge (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier a w h) :
    latticeBondEdge (rectanglePrimalEdgeBond e) =
      rectanglePrimalEdgeToSquareEdge e := Equiv.apply_symm_apply wholePlaneBondEdgeEquiv
    _

private theorem rectanglePrimalEdgeBond_toSym2 (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier a w h) :
    (rectanglePrimalEdgeBond e).toSym2 =
      Sym2.map (fun z : RectangleVertex a w h => z.val) e.1 := congrArg Subtype.val (rectanglePrimalEdgeBond_edge a w h e)

private theorem rectanglePrimalEdgeBond_endpoints_mem (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier a w h) :
    (rectanglePrimalEdgeBond e).source ∈ latticeRectangle a w h ∧
    (rectanglePrimalEdgeBond e).target ∈ latticeRectangle a w h := by
  let p := e.1.out
  have hrepr : s(p.1, p.2) = e.1 := Quot.out_eq _
  have hm : Sym2.map (fun z : RectangleVertex a w h => z.val) e.1 =
      s(p.1.val, p.2.val) := by
    rw [← hrepr]
    rfl
  have heq : s((rectanglePrimalEdgeBond e).source,
      (rectanglePrimalEdgeBond e).target) = s(p.1.val, p.2.val) := by
    exact (rectanglePrimalEdgeBond_toSym2 a w h e).trans hm
  grind

/-- The true dual bond crossing a rectangle edge, indexed by that original edge. -/
noncomputable def rectangleCrossingDualBond {a : LatticeVertex} {w h : ℕ}
    (e : rectanglePrimalEdgeCarrier a w h) : LatticeBond :=
  dualBondOfPrimal (rectanglePrimalEdgeBond e)

private theorem dualBondOfPrimal_endpoints_expanded
    (a : LatticeVertex) (w h : ℕ) (b : LatticeBond)
    (hs : b.source ∈ latticeRectangle a w h)
    (ht : b.target ∈ latticeRectangle a w h) :
    (dualBondOfPrimal b).source ∈ rectangleDualExpanded a w h ∧
    (dualBondOfPrimal b).target ∈ rectangleDualExpanded a w h := by
  rcases b with ⟨⟨x,y⟩, ax⟩
  cases ax
  · have hs' := (mem_latticeRectangle a (x,y) w h).mp hs
    simp only [dualBondOfPrimal, LatticeBond.source, LatticeBond.target,
      rectangleDualExpanded]
    grind [mem_latticeRectangle]
  · have hs' := (mem_latticeRectangle a (x,y) w h).mp hs
    simp only [dualBondOfPrimal, LatticeBond.source, LatticeBond.target,
      rectangleDualExpanded]
    grind [mem_latticeRectangle]

 theorem rectangleCrossingDualBond_endpoints_expanded
    (a : LatticeVertex) (w h : ℕ) (e : rectanglePrimalEdgeCarrier a w h) :
    (rectangleCrossingDualBond e).source ∈ rectangleDualExpanded a w h ∧
    (rectangleCrossingDualBond e).target ∈ rectangleDualExpanded a w h := dualBondOfPrimal_endpoints_expanded a w h
    _
    (rectanglePrimalEdgeBond_endpoints_mem a w h e).1
    (rectanglePrimalEdgeBond_endpoints_mem a w h e).2

/-- A dual edge retains its actual original-edge label and crossing bond. This
carrier is a multigraph edge type: endpoint coincidence after wiring never
identifies distinct original bonds. -/
structure RectangleDualEdgeCarrier (a : LatticeVertex) (w h : ℕ) where
  primalEdge : rectanglePrimalEdgeCarrier a w h
  crossingBond : LatticeBond
  crossingBond_eq : crossingBond = rectangleCrossingDualBond primalEdge

instance rectanglePrimalEdgeCarrierFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (rectanglePrimalEdgeCarrier a w h) := by
  classical
  exact Fintype.ofFinite _

/-- Every original edge gives its unique crossing dual edge, retaining the
original edge label. -/
def rectanglePrimalDualEdgeEquiv (a : LatticeVertex) (w h : ℕ) :
    rectanglePrimalEdgeCarrier a w h ≃ RectangleDualEdgeCarrier a w h where
  toFun e := ⟨e, rectangleCrossingDualBond e, rfl⟩
  invFun d := d.primalEdge
  left_inv _ := rfl
  right_inv d := by
    cases d with
    | mk primal crossing hc =>
      subst crossing
      rfl

@[simp] theorem rectangleDualEdge_crossedPrimalBond (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    primalBondOfDual e.crossingBond = rectanglePrimalEdgeBond e.primalEdge := by
  rw [e.crossingBond_eq]
  simp [rectangleCrossingDualBond]

@[simp] theorem rectangleDualEdge_crossing_originalEdge (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    latticeBondEdge (primalBondOfDual e.crossingBond) =
      rectanglePrimalEdgeToSquareEdge e.primalEdge := by
  grind [rectangleDualEdge_crossedPrimalBond, rectanglePrimalEdgeBond_edge]

/-- Endpoint maps into the expanded face-base rectangle, before any boundary
vertices are wired together. -/
def rectangleDualEdgeSource {a : LatticeVertex} {w h : ℕ}
    (e : RectangleDualEdgeCarrier a w h) :
    {z // z ∈ rectangleDualExpanded a w h} := by
  refine ⟨e.crossingBond.source, ?_⟩
  rw [e.crossingBond_eq]
  exact (rectangleCrossingDualBond_endpoints_expanded a w h e.primalEdge).1

def rectangleDualEdgeTarget {a : LatticeVertex} {w h : ℕ}
    (e : RectangleDualEdgeCarrier a w h) :
    {z // z ∈ rectangleDualExpanded a w h} := by
  refine ⟨e.crossingBond.target, ?_⟩
  rw [e.crossingBond_eq]
  exact (rectangleCrossingDualBond_endpoints_expanded a w h e.primalEdge).2

@[simp] theorem rectangleDualEdgeSource_val (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    (rectangleDualEdgeSource e).val = e.crossingBond.source := rfl

@[simp] theorem rectangleDualEdgeTarget_val (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    (rectangleDualEdgeTarget e).val = e.crossingBond.target := rfl

theorem rectangleDualEdgeSource_faceBase (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    (rectangleDualEdgeSource e).val =
      (rectanglePrimalEdgeBond e.primalEdge).faceBase false := by
  simp [rectangleDualEdgeSource_val, e.crossingBond_eq, rectangleCrossingDualBond, PottsDiscontinuity.FK.Medial.dualBondOfPrimal_source]

theorem rectangleDualEdgeTarget_faceBase (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    (rectangleDualEdgeTarget e).val =
      (rectanglePrimalEdgeBond e.primalEdge).faceBase true := by
  simp [rectangleDualEdgeTarget_val, e.crossingBond_eq, rectangleCrossingDualBond, PottsDiscontinuity.FK.Medial.dualBondOfPrimal_target]

/-- The open primal subset `A` determines the open dual complement. -/

def finsetComplementEquiv (α : Type*) [Fintype α] [DecidableEq α] :
    Finset α ≃ Finset α where
  toFun s := Finset.univ \ s
  invFun s := Finset.univ \ s
  left_inv := by
    intro s
    ext x
    simp
  right_inv := by
    intro s
    ext x
    simp

noncomputable def rectangleDualComplementEquiv (a : LatticeVertex) (w h : ℕ) :
    Finset (rectanglePrimalEdgeCarrier a w h) ≃
      Finset (RectangleDualEdgeCarrier a w h) := (finsetComplementEquiv _).trans (Equiv.finsetCongr (rectanglePrimalDualEdgeEquiv a w h))

@[simp] theorem mem_rectangleDualComplementEquiv
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (e : RectangleDualEdgeCarrier a w h) :
    e ∈ rectangleDualComplementEquiv a w h A ↔ e.primalEdge ∉ A := by
  classical
  simp [rectangleDualComplementEquiv, finsetComplementEquiv,
    Equiv.finsetCongr_apply, rectanglePrimalDualEdgeEquiv]

theorem rectangleDualComplement_card_add (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    A.card + (rectangleDualComplementEquiv a w h A).card =
      Fintype.card (rectanglePrimalEdgeCarrier a w h) := by
  classical
  have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  have hmap : (rectangleDualComplementEquiv a w h A).card =
      (Finset.univ \ A).card := by
    simp [rectangleDualComplementEquiv, finsetComplementEquiv]
  grind

/-- The expanded dual vertex type, before the boundary is wired. -/
abbrev RectangleDualVertex (a : LatticeVertex) (w h : ℕ) :=
  {z // z ∈ rectangleDualExpanded a w h}

/-- The unordered endpoint pair of a labelled crossing edge. -/
def rectangleDualCarrierPair (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) : Sym2 (RectangleDualVertex a w h) :=
  s(rectangleDualEdgeSource e, rectangleDualEdgeTarget e)

 theorem rectangleDualCarrierPair_injective (a : LatticeVertex) (w h : ℕ) :
    Function.Injective (rectangleDualCarrierPair a w h) := by
  intro e f hef
  have hcross := LatticeBond.toSym2_injective (congrArg (Sym2.map (fun z : RectangleDualVertex a w h => z.1)) hef)
  have hsub :=
    (Sym2.map.injective Subtype.val_injective) (congrArg Subtype.val (by
      have hb := congrArg latticeBondEdge (by
        simpa only [rectangleDualEdge_crossedPrimalBond] using
          congrArg primalBondOfDual hcross)
      simpa only [rectanglePrimalEdgeBond_edge] using hb))
  have he := Subtype.ext hsub
  cases e with
  | mk pe cb hcb =>
    simp_all

/-- The actual finite simple dual graph on expanded face bases. Its edges are
exactly the crossing pairs indexed by original rectangle edges. -/
noncomputable def rectangleDualGraph (a : LatticeVertex) (w h : ℕ) :
    SimpleGraph (RectangleDualVertex a w h) :=
  SimpleGraph.fromEdgeSet (Set.range (rectangleDualCarrierPair a w h))

private theorem rectangleDualCarrierPair_not_diag (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    ¬ (rectangleDualCarrierPair a w h e).IsDiag := fun hd => LatticeBond.source_ne_target e.crossingBond (congrArg Subtype.val (Sym2.mk_isDiag_iff.mp hd))

private theorem rectangleDualCarrierPair_ne (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) (u : RectangleDualVertex a w h) :
    rectangleDualCarrierPair a w h e ≠ s(u,u) := by
  intro he
  exact rectangleDualCarrierPair_not_diag a w h e (by simp_all)

@[simp] theorem rectangleDualGraph_adj_iff (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleDualVertex a w h) :
    (rectangleDualGraph a w h).Adj u v ↔
      ∃ e,
        s(u, v) = rectangleDualCarrierPair a w h e := by
  constructor
  · rintro ⟨⟨e, he⟩, hne⟩
    refine ⟨e, he.symm⟩
  · rintro ⟨e, he⟩
    refine ⟨⟨e, he.symm⟩, ?_⟩
    intro huv
    apply rectangleDualCarrierPair_ne a w h e u
    calc
      _ = s(u, v) := he.symm
      _ = _ := by rw [huv]

theorem rectangleDualGraph_edgeSet_eq_range (a : LatticeVertex) (w h : ℕ) :
    (rectangleDualGraph a w h).edgeSet = Set.range (rectangleDualCarrierPair a w h) := by
  rw [rectangleDualGraph, SimpleGraph.edgeSet_fromEdgeSet]
  ext pair
  constructor
  · grind
  · rintro ⟨e, rfl⟩
    exact ⟨⟨e, rfl⟩, rectangleDualCarrierPair_not_diag a w h e⟩

/-- Every graph edge has exactly one original crossing-edge label, prior to
boundary wiring. -/
noncomputable def rectangleDualGraphEdgeEquiv (a : LatticeVertex) (w h : ℕ) :
    RectangleDualEdgeCarrier a w h ≃ (rectangleDualGraph a w h).edgeSet := by
  classical
  apply Equiv.ofBijective
    (fun e => ⟨rectangleDualCarrierPair a w h e, by
      simp_all [rectangleDualGraph_edgeSet_eq_range]⟩)
  constructor
  · intro e f hef
    grind [rectangleDualCarrierPair_injective]
  · intro f
    have hf : f.1 ∈ Set.range (rectangleDualCarrierPair a w h) := by
      rw [← rectangleDualGraph_edgeSet_eq_range]
      exact f.2
    grind [Subtype.ext]

/-- The wired boundary condition on the expanded dual vertex rectangle. -/
def rectangleDualBoundaryCondition (a : LatticeVertex) (w h : ℕ) :
    BoundaryCondition (RectangleDualVertex a w h) :=
  BoundaryCondition.wired {z | z.1 ∈ rectangleDualBoundary a w h}

@[simp] theorem rectangleDualBoundaryCondition_rel (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleDualVertex a w h) :
    (rectangleDualBoundaryCondition a w h).partition.r u v ↔
      u = v ∨ u.1 ∈ rectangleDualBoundary a w h ∧
        v.1 ∈ rectangleDualBoundary a w h := by
  rfl

end
end PottsDiscontinuity.FK
