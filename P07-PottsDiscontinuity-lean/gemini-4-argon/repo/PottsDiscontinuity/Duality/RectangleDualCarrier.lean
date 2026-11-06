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
    a.1 ≤ z.1 ∧ z.1 < a.1 + (w : ℤ) ∧
    a.2 ≤ z.2 ∧ z.2 < a.2 + (h : ℤ)

/-- Every expanded dual vertex not strictly internal is part of the wired
boundary/exterior class, including isolated corners and degenerate boxes. -/
def rectangleDualBoundary (a : LatticeVertex) (w h : ℕ) : Finset LatticeVertex :=
  (rectangleDualExpanded a w h).filter fun z => z ∉ rectangleDualInterior a w h

@[simp] theorem rectangleDualInterior_eq_empty_width_zero
    (a : LatticeVertex) (h : ℕ) : rectangleDualInterior a 0 h = ∅ := by
  ext z
  simp [rectangleDualInterior]
  omega

@[simp] theorem rectangleDualInterior_eq_empty_height_zero
    (a : LatticeVertex) (w : ℕ) : rectangleDualInterior a w 0 = ∅ := by
  ext z
  simp [rectangleDualInterior]

@[simp] theorem rectangleDualExpanded_card (a : LatticeVertex) (w h : ℕ) :
    (rectangleDualExpanded a w h).card = (w + 2) * (h + 2) := by
  simp [rectangleDualExpanded, card_latticeRectangle]

@[simp] theorem rectangleDualBoundary_eq_expanded_width_zero
    (a : LatticeVertex) (h : ℕ) : rectangleDualBoundary a 0 h =
      rectangleDualExpanded a 0 h := by
  simp [rectangleDualBoundary, rectangleDualInterior_eq_empty_width_zero]

@[simp] theorem rectangleDualBoundary_eq_expanded_height_zero
    (a : LatticeVertex) (w : ℕ) : rectangleDualBoundary a w 0 =
      rectangleDualExpanded a w 0 := by
  simp [rectangleDualBoundary, rectangleDualInterior_eq_empty_height_zero]

/-- A normalized original bond whose two endpoints lie in the primal rectangle. -/
abbrev RectanglePrimalBond (a : LatticeVertex) (w h : ℕ) :=
  {b : LatticeBond // b.source ∈ latticeRectangle a w h ∧
    b.target ∈ latticeRectangle a w h}

/-- The finite carrier of original primal edges in the rectangle. -/
def rectanglePrimalEdgeCarrier (a : LatticeVertex) (w h : ℕ) :=
  (rectangleGraph a w h).edgeSet

/-- Embed an actual induced-rectangle edge into the whole-plane edge carrier. -/
noncomputable def rectanglePrimalEdgeToSquareEdge (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier a w h) : squareLattice.edgeSet := by
  let p := e.1.out
  have hrepr : s(p.1, p.2) = e.1 := Quot.out_eq _
  have hadj : s(p.1, p.2) ∈ (rectangleGraph a w h).edgeSet := hrepr.symm ▸ e.2
  refine ⟨Sym2.map Subtype.val e.1, ?_⟩
  rw [← hrepr]
  exact squareLattice.mem_edgeSet.mpr ((rectangleGraph_adj_iff a w h p.1 p.2).mp hadj)

noncomputable def rectanglePrimalEdgeBond (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier a w h) : LatticeBond :=
  wholePlaneBondEdgeEquiv.symm (rectanglePrimalEdgeToSquareEdge a w h e)

private theorem rectanglePrimalEdgeBond_edge (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier a w h) :
    latticeBondEdge (rectanglePrimalEdgeBond a w h e) =
      rectanglePrimalEdgeToSquareEdge a w h e :=
  wholePlaneBondEdgeEquiv.apply_symm_apply _

private theorem rectanglePrimalEdgeBond_endpoints_mem (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier a w h) :
    (rectanglePrimalEdgeBond a w h e).source ∈ latticeRectangle a w h ∧
    (rectanglePrimalEdgeBond a w h e).target ∈ latticeRectangle a w h := by
  let p := e.1.out
  have heq : s((rectanglePrimalEdgeBond a w h e).source,
      (rectanglePrimalEdgeBond a w h e).target) = s(p.1.val, p.2.val) := by
    have hb := congrArg Subtype.val (rectanglePrimalEdgeBond_edge a w h e)
    change (rectanglePrimalEdgeBond a w h e).toSym2 = Sym2.map Subtype.val e.1 at hb
    rw [← Quot.out_eq e.1] at hb
    exact hb
  rcases Sym2.eq_iff.mp heq with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;> [exact ⟨hs ▸ p.1.2, ht ▸ p.2.2⟩; exact ⟨hs ▸ p.2.2, ht ▸ p.1.2⟩]

/-- The true dual bond crossing a rectangle edge, indexed by that original edge. -/
noncomputable def rectangleCrossingDualBond (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier a w h) : LatticeBond :=
  dualBondOfPrimal (rectanglePrimalEdgeBond a w h e)

private theorem dualBondOfPrimal_endpoints_expanded
    (a : LatticeVertex) (w h : ℕ) (b : LatticeBond)
    (hs : b.source ∈ latticeRectangle a w h)
    (ht : b.target ∈ latticeRectangle a w h) :
    (dualBondOfPrimal b).source ∈ rectangleDualExpanded a w h ∧
    (dualBondOfPrimal b).target ∈ rectangleDualExpanded a w h := by
  rcases b with ⟨⟨x, y⟩, ax⟩
  rw [mem_latticeRectangle] at hs ht
  cases ax <;> simp only [dualBondOfPrimal, LatticeBond.source, LatticeBond.target,
    rectangleDualExpanded, mem_latticeRectangle] at hs ht ⊢ <;> omega

theorem rectangleCrossingDualBond_endpoints_expanded
    (a : LatticeVertex) (w h : ℕ) (e : rectanglePrimalEdgeCarrier a w h) :
    (rectangleCrossingDualBond a w h e).source ∈ rectangleDualExpanded a w h ∧
    (rectangleCrossingDualBond a w h e).target ∈ rectangleDualExpanded a w h :=
  dualBondOfPrimal_endpoints_expanded a w h
    (rectanglePrimalEdgeBond a w h e)
    (rectanglePrimalEdgeBond_endpoints_mem a w h e).1
    (rectanglePrimalEdgeBond_endpoints_mem a w h e).2

/-- A dual edge retains its actual original-edge label and crossing bond. This
carrier is a multigraph edge type: endpoint coincidence after wiring never
identifies distinct original bonds. -/
structure RectangleDualEdgeCarrier (a : LatticeVertex) (w h : ℕ) where
  primalEdge : rectanglePrimalEdgeCarrier a w h
  crossingBond : LatticeBond
  crossingBond_eq : crossingBond = rectangleCrossingDualBond a w h primalEdge

instance rectanglePrimalEdgeCarrierFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (rectanglePrimalEdgeCarrier a w h) := by
  letI : Finite (rectanglePrimalEdgeCarrier a w h) :=
    Finite.of_injective (fun e : rectanglePrimalEdgeCarrier a w h => e.1) Subtype.val_injective
  exact Fintype.ofFinite _

/-- Every original edge gives its unique crossing dual edge, retaining the
original edge label. -/
def rectanglePrimalDualEdgeEquiv (a : LatticeVertex) (w h : ℕ) :
    rectanglePrimalEdgeCarrier a w h ≃ RectangleDualEdgeCarrier a w h where
  toFun e := ⟨e, rectangleCrossingDualBond a w h e, rfl⟩
  invFun d := d.primalEdge
  left_inv _ := rfl
  right_inv := fun ⟨_, _, rfl⟩ => rfl

instance rectangleDualEdgeCarrierFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (RectangleDualEdgeCarrier a w h) :=
  Fintype.ofEquiv (rectanglePrimalEdgeCarrier a w h)
    (rectanglePrimalDualEdgeEquiv a w h)

@[simp] theorem rectangleDualEdge_crossedPrimalBond (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    primalBondOfDual e.crossingBond = rectanglePrimalEdgeBond a w h e.primalEdge := by
  simp [e.crossingBond_eq, rectangleCrossingDualBond]

@[simp] theorem rectangleDualEdge_crossing_originalEdge (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    latticeBondEdge (primalBondOfDual e.crossingBond) =
      rectanglePrimalEdgeToSquareEdge a w h e.primalEdge := by
  rw [rectangleDualEdge_crossedPrimalBond]
  exact rectanglePrimalEdgeBond_edge a w h e.primalEdge

/-- Endpoint maps into the expanded face-base rectangle, before any boundary
vertices are wired together. -/
def rectangleDualEdgeSource (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    {z // z ∈ rectangleDualExpanded a w h} :=
  ⟨e.crossingBond.source, e.crossingBond_eq ▸ (rectangleCrossingDualBond_endpoints_expanded a w h e.primalEdge).1⟩

def rectangleDualEdgeTarget (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    {z // z ∈ rectangleDualExpanded a w h} :=
  ⟨e.crossingBond.target, e.crossingBond_eq ▸ (rectangleCrossingDualBond_endpoints_expanded a w h e.primalEdge).2⟩

@[simp] theorem rectangleDualEdgeSource_val (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    (rectangleDualEdgeSource a w h e).val = e.crossingBond.source := rfl

@[simp] theorem rectangleDualEdgeTarget_val (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    (rectangleDualEdgeTarget a w h e).val = e.crossingBond.target := rfl

theorem rectangleDualEdgeSource_faceBase (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    (rectangleDualEdgeSource a w h e).val =
      (rectanglePrimalEdgeBond a w h e.primalEdge).faceBase false := by
  simp [rectangleDualEdgeSource_val, e.crossingBond_eq, rectangleCrossingDualBond,
    PottsDiscontinuity.FK.Medial.dualBondOfPrimal_source]

theorem rectangleDualEdgeTarget_faceBase (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    (rectangleDualEdgeTarget a w h e).val =
      (rectanglePrimalEdgeBond a w h e.primalEdge).faceBase true := by
  simp [rectangleDualEdgeTarget_val, e.crossingBond_eq, rectangleCrossingDualBond,
    PottsDiscontinuity.FK.Medial.dualBondOfPrimal_target]

/-- The open primal subset `A` determines the open dual complement. -/
def finsetComplementEquiv (α : Type*) [Fintype α] [DecidableEq α] :
    Finset α ≃ Finset α where
  toFun s := Finset.univ \ s
  invFun s := Finset.univ \ s
  left_inv s := by ext; simp
  right_inv s := by ext; simp

noncomputable def rectangleDualComplementEquiv (a : LatticeVertex) (w h : ℕ) :
    Finset (rectanglePrimalEdgeCarrier a w h) ≃
      Finset (RectangleDualEdgeCarrier a w h) := by
  classical
  exact (finsetComplementEquiv _).trans
    (Equiv.finsetCongr (rectanglePrimalDualEdgeEquiv a w h))

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
  simpa [rectangleDualComplementEquiv, finsetComplementEquiv, Equiv.finsetCongr_apply,
    Nat.add_comm] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)

/-- The expanded dual vertex type, before the boundary is wired. -/
abbrev RectangleDualVertex (a : LatticeVertex) (w h : ℕ) :=
  {z // z ∈ rectangleDualExpanded a w h}

/-- The unordered endpoint pair of a labelled crossing edge. -/
def rectangleDualCarrierPair (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) : Sym2 (RectangleDualVertex a w h) :=
  s(rectangleDualEdgeSource a w h e, rectangleDualEdgeTarget a w h e)

theorem rectangleDualCarrierPair_injective (a : LatticeVertex) (w h : ℕ) :
    Function.Injective (rectangleDualCarrierPair a w h) := by
  rintro ⟨pe, cb, hcb⟩ ⟨pf, cf, hcf⟩ hef
  have hmap := congrArg (Sym2.map (fun z : RectangleDualVertex a w h => z.1)) hef
  change cb.toSym2 = cf.toSym2 at hmap
  have hcross : cb = cf := LatticeBond.toSym2_injective hmap
  subst hcross
  have hprimal := congrArg (fun b => (latticeBondEdge (primalBondOfDual b)).val)
    (hcb.symm.trans hcf)
  simp only [rectangleCrossingDualBond, primalBondOfDual_dualBondOfPrimal,
    rectanglePrimalEdgeBond_edge, rectanglePrimalEdgeToSquareEdge] at hprimal
  cases Subtype.ext ((Sym2.map.injective Subtype.val_injective) hprimal)
  rfl

/-- The actual finite simple dual graph on expanded face bases. Its edges are
exactly the crossing pairs indexed by original rectangle edges. -/
noncomputable def rectangleDualGraph (a : LatticeVertex) (w h : ℕ) :
    SimpleGraph (RectangleDualVertex a w h) :=
  SimpleGraph.fromEdgeSet (Set.range (rectangleDualCarrierPair a w h))

private theorem rectangleDualCarrierPair_not_diag (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    ¬ (rectangleDualCarrierPair a w h e).IsDiag := by
  intro hd
  exact e.crossingBond.source_ne_target <|
    congrArg Subtype.val (Sym2.mk_isDiag_iff.mp hd)

@[simp] theorem rectangleDualGraph_adj_iff (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleDualVertex a w h) :
    (rectangleDualGraph a w h).Adj u v ↔
      ∃ e : RectangleDualEdgeCarrier a w h,
        s(u, v) = rectangleDualCarrierPair a w h e := by
  rw [rectangleDualGraph, SimpleGraph.fromEdgeSet_adj]
  exact ⟨fun ⟨⟨e, he⟩, _⟩ => ⟨e, he.symm⟩, fun ⟨e, he⟩ =>
    ⟨⟨e, he.symm⟩, fun huv => rectangleDualCarrierPair_not_diag a w h e
      (he ▸ huv ▸ Sym2.diag_isDiag u)⟩⟩

theorem rectangleDualGraph_edgeSet_eq_range (a : LatticeVertex) (w h : ℕ) :
    (rectangleDualGraph a w h).edgeSet = Set.range (rectangleDualCarrierPair a w h) := by
  rw [rectangleDualGraph, SimpleGraph.edgeSet_fromEdgeSet]
  ext pair
  exact ⟨fun ⟨h, _⟩ => h, fun ⟨e, he⟩ => ⟨⟨e, he⟩, he ▸ rectangleDualCarrierPair_not_diag a w h e⟩⟩

/-- Every graph edge has exactly one original crossing-edge label, prior to
boundary wiring. -/
noncomputable def rectangleDualGraphEdgeEquiv (a : LatticeVertex) (w h : ℕ) :
    RectangleDualEdgeCarrier a w h ≃ (rectangleDualGraph a w h).edgeSet :=
  Equiv.ofBijective
    (fun e => ⟨rectangleDualCarrierPair a w h e, by
      rw [rectangleDualGraph_edgeSet_eq_range]; exact ⟨e, rfl⟩⟩)
    ⟨fun _ _ hef => rectangleDualCarrierPair_injective a w h (congrArg Subtype.val hef),
      fun f => by
        obtain ⟨e, he⟩ : f.1 ∈ Set.range (rectangleDualCarrierPair a w h) := by
          rw [← rectangleDualGraph_edgeSet_eq_range]; exact f.2
        exact ⟨e, Subtype.ext he⟩⟩

/-- The wired boundary condition on the expanded dual vertex rectangle. -/
def rectangleDualBoundaryCondition (a : LatticeVertex) (w h : ℕ) :
    BoundaryCondition (RectangleDualVertex a w h) :=
  BoundaryCondition.wired {z | z.1 ∈ rectangleDualBoundary a w h}

@[simp] theorem rectangleDualBoundaryCondition_rel (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleDualVertex a w h) :
    (rectangleDualBoundaryCondition a w h).partition.r u v ↔
      u = v ∨ u.1 ∈ rectangleDualBoundary a w h ∧
        v.1 ∈ rectangleDualBoundary a w h := Iff.rfl

end
end PottsDiscontinuity.FK
