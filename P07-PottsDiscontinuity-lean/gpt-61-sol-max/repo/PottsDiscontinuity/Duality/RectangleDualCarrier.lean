/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

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
def rectangleDualInterior (a : LatticeVertex) (w h : ℕ)  :=
  (rectangleDualExpanded a w h).filter fun z =>
    a.1 ≤ z.1 ∧ z.1 < a.1 + (w : ℤ) ∧
    a.2 ≤ z.2 ∧ z.2 < a.2 + (h : ℤ)

/-- Every expanded dual vertex not strictly internal is part of the wired
boundary/exterior class, including isolated corners and degenerate boxes. -/
def rectangleDualBoundary (a : LatticeVertex) (w h : ℕ)  :=
  (rectangleDualExpanded a w h).filter fun z => z ∉ rectangleDualInterior a w h










@[simp] theorem rectangleDualExpanded_card (a : LatticeVertex)  (w h : ℕ) :
    (rectangleDualExpanded a w h).card = (w + 2) * (h + 2) := by
  simp [rectangleDualExpanded, card_latticeRectangle]







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
  
  
  refine ⟨Sym2.map (fun z : RectangleVertex a w h => z.val) e.1, ?_⟩
  have heq : Sym2.map (fun z : RectangleVertex a w h => z.val) e.1 =
      s(p.1.val, p.2.val) := by
    rw [← hrepr]
    rfl
  rw [heq]
  exact squareLattice.mem_edgeSet.mpr (by
                                           bound)

noncomputable def rectanglePrimalEdgeBond (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier a w h)  :=
  wholePlaneBondEdgeEquiv.symm (rectanglePrimalEdgeToSquareEdge a w h e)

section

variable (a : LatticeVertex) (w h : ℕ) (e : rectanglePrimalEdgeCarrier a w h)
include e

private theorem rectanglePrimalEdgeBond_edge  :
    latticeBondEdge (rectanglePrimalEdgeBond a w h e) =
      rectanglePrimalEdgeToSquareEdge a w h e := Equiv.apply_symm_apply wholePlaneBondEdgeEquiv (rectanglePrimalEdgeToSquareEdge a w h e)

private theorem rectanglePrimalEdgeBond_toSym2  :
    (rectanglePrimalEdgeBond a w h e).toSym2 =
      Sym2.map (fun z : RectangleVertex a w h => z.val) e.1 := congrArg Subtype.val (rectanglePrimalEdgeBond_edge a w h e)

private theorem rectanglePrimalEdgeBond_endpoints_mem  :
    (rectanglePrimalEdgeBond a w h e).source ∈ latticeRectangle a w h ∧
    (rectanglePrimalEdgeBond a w h e).target ∈ latticeRectangle a w h := by
  let p := e.1.out
  have hrepr : s(p.1, p.2) = e.1 := Quot.out_eq _
  
  have hm : Sym2.map (fun z  => z.val) e.1 =
      s(p.1.val, p.2.val) := by
    rw [← hrepr]
    rfl
  
  rcases Sym2.eq_iff.mp (by
                           simpa [LatticeBond.toSym2] using (rectanglePrimalEdgeBond_toSym2 a w h e).trans hm) with ⟨hs, ht⟩ | ⟨hs, ht⟩
  all_goals simp_all

end

/-- The true dual bond crossing a rectangle edge, indexed by that original edge. -/
noncomputable def rectangleCrossingDualBond (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier a w h)  :=
  dualBondOfPrimal (rectanglePrimalEdgeBond a w h e)

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
    constructor <;> rw [mem_latticeRectangle] <;> norm_num <;> omega
  · have hs' := (mem_latticeRectangle a (x,y) w h).mp hs
    
    simp only [dualBondOfPrimal, LatticeBond.source, LatticeBond.target,
      rectangleDualExpanded]
    constructor <;> rw [mem_latticeRectangle] <;> norm_num <;> omega

 theorem rectangleCrossingDualBond_endpoints_expanded
    (a : LatticeVertex) (w h : ℕ) (e : rectanglePrimalEdgeCarrier a w h) :
    (rectangleCrossingDualBond a w h e).source ∈ rectangleDualExpanded a w h ∧
    (rectangleCrossingDualBond a w h e).target ∈ rectangleDualExpanded a w h := dualBondOfPrimal_endpoints_expanded a w h (rectanglePrimalEdgeBond a w h e)
                                                                                  (rectanglePrimalEdgeBond_endpoints_mem a w h e).left (rectanglePrimalEdgeBond_endpoints_mem a w h e).right

/-- A dual edge retains its actual original-edge label and crossing bond. This
carrier is a multigraph edge type: endpoint coincidence after wiring never
identifies distinct original bonds. -/
structure RectangleDualEdgeCarrier (a : LatticeVertex) (w h : ℕ) where
  primalEdge : rectanglePrimalEdgeCarrier a w h
  crossingBond : LatticeBond
  crossingBond_eq : crossingBond = rectangleCrossingDualBond a w h primalEdge

instance rectanglePrimalEdgeCarrierFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (rectanglePrimalEdgeCarrier a w h) := by
  classical
  letI : Fintype (RectangleVertex a w h) := Fintype.ofFinite _
  letI : Fintype (Sym2 (RectangleVertex a w h)) := inferInstance
  letI : Finite (rectanglePrimalEdgeCarrier a w h) :=
    Finite.of_injective (fun e : rectanglePrimalEdgeCarrier a w h => e.1)
      Subtype.val_injective
  exact Fintype.ofFinite _

/-- Every original edge gives its unique crossing dual edge, retaining the
original edge label. -/
def rectanglePrimalDualEdgeEquiv (a : LatticeVertex) (w h : ℕ) :
    rectanglePrimalEdgeCarrier a w h ≃ RectangleDualEdgeCarrier a w h where
  toFun e := ⟨e, rectangleCrossingDualBond a w h e, rfl⟩
  invFun d := d.primalEdge
  left_inv _ := rfl
  right_inv d := by
    cases d with
    | mk primal crossing hc =>
      subst crossing
      rfl

instance rectangleDualEdgeCarrierFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (RectangleDualEdgeCarrier a w h) :=
  Fintype.ofEquiv (rectanglePrimalEdgeCarrier a w h)
    (rectanglePrimalDualEdgeEquiv a w h)

section

variable (a : LatticeVertex) (w h : ℕ) (e : RectangleDualEdgeCarrier a w h)


@[simp] theorem rectangleDualEdge_crossedPrimalBond  :
    primalBondOfDual e.crossingBond = rectanglePrimalEdgeBond a w h e.primalEdge := by
  rw [e.crossingBond_eq]
  simp [rectangleCrossingDualBond]

@[simp] theorem rectangleDualEdge_crossing_originalEdge  :
    latticeBondEdge (primalBondOfDual e.crossingBond) =
      rectanglePrimalEdgeToSquareEdge a w h e.primalEdge := by
  simp_all [rectangleDualEdge_crossedPrimalBond, rectanglePrimalEdgeBond_edge]

end

/-- Endpoint maps into the expanded face-base rectangle, before any boundary
vertices are wired together. -/
def rectangleDualEdgeSource (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    {z // z ∈ rectangleDualExpanded a w h} := by
  refine ⟨e.crossingBond.source, ?_⟩
  rw [e.crossingBond_eq]
  exact (rectangleCrossingDualBond_endpoints_expanded a w h e.primalEdge).1

def rectangleDualEdgeTarget (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    {z // z ∈ rectangleDualExpanded a w h} := by
  refine ⟨e.crossingBond.target, ?_⟩
  rw [e.crossingBond_eq]
  exact (rectangleCrossingDualBond_endpoints_expanded a w h e.primalEdge).2

section

variable (a : LatticeVertex) (w h : ℕ) (e : RectangleDualEdgeCarrier a w h)


@[simp] theorem rectangleDualEdgeSource_val  :
    (rectangleDualEdgeSource a w h e).val = e.crossingBond.source := rfl

@[simp] theorem rectangleDualEdgeTarget_val  :
    (rectangleDualEdgeTarget a w h e).val = e.crossingBond.target := rfl

theorem rectangleDualEdgeSource_faceBase  :
    (rectangleDualEdgeSource a w h e).val =
      (rectanglePrimalEdgeBond a w h e.primalEdge).faceBase false := by
  rw [rectangleDualEdgeSource_val, e.crossingBond_eq]
  simp [rectangleCrossingDualBond, PottsDiscontinuity.FK.Medial.dualBondOfPrimal_source]

theorem rectangleDualEdgeTarget_faceBase  :
    (rectangleDualEdgeTarget a w h e).val =
      (rectanglePrimalEdgeBond a w h e.primalEdge).faceBase true := by
  rw [rectangleDualEdgeTarget_val, e.crossingBond_eq]
  simp [rectangleCrossingDualBond, PottsDiscontinuity.FK.Medial.dualBondOfPrimal_target]

end

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
      Finset (RectangleDualEdgeCarrier a w h) := by
  classical
  letI : Fintype (RectangleDualEdgeCarrier a w h) := inferInstance
  exact (finsetComplementEquiv _).trans
    (Equiv.finsetCongr (rectanglePrimalDualEdgeEquiv a w h))

section

variable (a : LatticeVertex) (w h : ℕ) (A : Finset (rectanglePrimalEdgeCarrier a w h))


@[simp] theorem mem_rectangleDualComplementEquiv
    
    (e : RectangleDualEdgeCarrier a w h) :
    e ∈ rectangleDualComplementEquiv a w h A ↔ e.primalEdge ∉ A := by
  simp_all [rectangleDualComplementEquiv, finsetComplementEquiv, rectanglePrimalDualEdgeEquiv]

theorem rectangleDualComplement_card_add  :
    A.card + (rectangleDualComplementEquiv a w h A).card =
      Fintype.card (rectanglePrimalEdgeCarrier a w h) := by
  
  
  have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  have hmap : (rectangleDualComplementEquiv a w h A).card =
      (Finset.univ \ A).card := by
    simp [rectangleDualComplementEquiv, finsetComplementEquiv,
      Equiv.finsetCongr_apply, Finset.card_map]
  grind

end

/-- The expanded dual vertex type, before the boundary is wired. -/
abbrev RectangleDualVertex (a : LatticeVertex) (w h : ℕ) :=
  {z // z ∈ rectangleDualExpanded a w h}

/-- The unordered endpoint pair of a labelled crossing edge. -/
def rectangleDualCarrierPair (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) : Sym2 (RectangleDualVertex a w h) :=
  s(rectangleDualEdgeSource a w h e, rectangleDualEdgeTarget a w h e)



 theorem rectangleDualCarrierPair_injective (a : LatticeVertex) (w h : ℕ) :
    Function.Injective (rectangleDualCarrierPair a w h) := by
  intro e f hef
  have hmap := congrArg (Sym2.map  fun z  => z.1 ) hef
  
  have hcross  := LatticeBond.toSym2_injective hmap
  have hprimal : rectanglePrimalEdgeBond a w h e.primalEdge =
      rectanglePrimalEdgeBond a w h f.primalEdge := by
    grind [primalBondOfDual, rectangleDualEdge_crossedPrimalBond]
  have hedge : rectanglePrimalEdgeToSquareEdge a w h e.primalEdge =
      rectanglePrimalEdgeToSquareEdge a w h f.primalEdge := by
    grind [latticeBondEdge, rectanglePrimalEdgeBond_edge]
  
  
  have he  := Subtype.ext ((Sym2.map.injective Subtype.val_injective) (congrArg Subtype.val hedge))
  cases e with
  | mk pe cb hcb =>
    simp_all

/-- The actual finite simple dual graph on expanded face bases. Its edges are
exactly the crossing pairs indexed by original rectangle edges. -/
noncomputable def rectangleDualGraph (a : LatticeVertex) (w h : ℕ)  :=
  SimpleGraph.fromEdgeSet (Set.range (rectangleDualCarrierPair a w h))

section

variable (a : LatticeVertex) (w h : ℕ)


private theorem rectangleDualCarrierPair_not_diag 
    (e : RectangleDualEdgeCarrier a w h) :
    ¬ (rectangleDualCarrierPair a w h e).IsDiag := by
  intro hd
  
  have hst := Sym2.mk_isDiag_iff.mp (by
                                       simpa [rectangleDualCarrierPair] using hd)
  
  exact e.crossingBond.source_ne_target (congrArg Subtype.val hst)

private theorem rectangleDualCarrierPair_ne 
    (e : RectangleDualEdgeCarrier a w h) (u : RectangleDualVertex a w h) :
    rectangleDualCarrierPair a w h e ≠ s(u,u) := fun he => rectangleDualCarrierPair_not_diag a w h e (Eq.mpr (congrArg Sym2.IsDiag he) (Sym2.diag_isDiag u))

@[simp] theorem rectangleDualGraph_adj_iff 
    (u v : RectangleDualVertex a w h) :
    (rectangleDualGraph a w h).Adj u v ↔
      ∃ e : RectangleDualEdgeCarrier a w h,
        s(u, v) = rectangleDualCarrierPair a w h e := by
  rw [rectangleDualGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · grind
  · grind [rectangleDualCarrierPair, rectangleDualCarrierPair_ne]

theorem rectangleDualGraph_edgeSet_eq_range  :
    (rectangleDualGraph a w h).edgeSet = Set.range (rectangleDualCarrierPair a w h) := by
  rw [rectangleDualGraph, SimpleGraph.edgeSet_fromEdgeSet]
  ext pair
  constructor
  · simp_all
  · rintro ⟨e, rfl⟩
    exact ⟨⟨e, rfl⟩, rectangleDualCarrierPair_not_diag a w h e⟩

end

/-- Every graph edge has exactly one original crossing-edge label, prior to
boundary wiring. -/
noncomputable def rectangleDualGraphEdgeEquiv (a : LatticeVertex) (w h : ℕ) :
    RectangleDualEdgeCarrier a w h ≃ (rectangleDualGraph a w h).edgeSet := by
  classical
  apply Equiv.ofBijective
     fun e => ⟨rectangleDualCarrierPair a w h e, by
      simp_all [rectangleDualGraph_edgeSet_eq_range]⟩ 
  constructor
  · intro e f hef
    exact rectangleDualCarrierPair_injective a w h (congrArg Subtype.val hef)
  · intro f
    have hf : f.1 ∈ Set.range (rectangleDualCarrierPair a w h) := by
      rw [← rectangleDualGraph_edgeSet_eq_range]
      exact f.2
    all_goals grind

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
