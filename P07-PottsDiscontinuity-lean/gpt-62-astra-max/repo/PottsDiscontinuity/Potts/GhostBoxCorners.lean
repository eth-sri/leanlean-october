module

public import PottsDiscontinuity.Potts.GhostBoxGeometry
public import PottsDiscontinuity.Potts.FiniteEnergyBounds

/-! The four corner edges omitted by the literal boundary term. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

variable (q : FK.Parameters) (n : ℕ) (b : Bool × Bool) (hn : 0 < n)
include n

include b in
def cornerPoint : ℤ × ℤ :=
  (if b.1 then (n : ℤ) else -(n : ℤ), if b.2 then (n : ℤ) else -(n : ℤ))

include b in
def cornerOutwardPoint : ℤ × ℤ :=
  ((cornerPoint n b).1, if b.2 then (n : ℤ) + 1 else -(n : ℤ) - 1)

theorem cornerPoint_mem : cornerPoint n b ∈ box n := by
  grind [mem_box_iff, cornerPoint]

theorem cornerOutwardPoint_mem :
    cornerOutwardPoint n b ∈ box (n + 1) := by
  grind [mem_box_iff, cornerOutwardPoint, cornerPoint]

theorem cornerOutwardPoint_not_mem :
    cornerOutwardPoint n b ∉ box n := by
  grind [mem_box_iff, cornerOutwardPoint, cornerPoint]

theorem cornerPoint_adj_outward :
    squareLattice.Adj (cornerPoint n b) (cornerOutwardPoint n b) := by
  grind [FK.squareLattice_adj_iff, cornerOutwardPoint, cornerPoint]

include b in
/-- The vertical outward edge at a corner; the horizontal one is retained. -/
def cornerCutEdge : OuterBoxEdge n :=
  ⟨s(⟨cornerPoint n b, box_subset_box_succ n (cornerPoint_mem n b)⟩,
      ⟨cornerOutwardPoint n b, cornerOutwardPoint_mem n b⟩),
    (squareLattice.induce _).mem_edgeSet.mpr (cornerPoint_adj_outward n b)⟩

include hn in
theorem cornerPoint_injective : Function.Injective (cornerPoint n) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  grind [cornerPoint]

include hn in
theorem cornerCutEdge_injective : Function.Injective (cornerCutEdge n) := by
  intro b c h
  have he : s(cornerPoint n b, cornerOutwardPoint n b) =
      s(cornerPoint n c, cornerOutwardPoint n c) :=
    congrArg (fun e : OuterBoxEdge n => Sym2.map Subtype.val e.val) h
  rcases Sym2.eq_iff.mp he with ⟨hbc, _⟩ | ⟨hbc, _⟩
  · exact cornerPoint_injective n hn hbc
  · exact (cornerOutwardPoint_not_mem n c (hbc ▸ cornerPoint_mem n b)).elim

def cornerCutEdges : Finset (OuterBoxEdge n) := by
  classical
  exact Finset.univ.image (cornerCutEdge n)

include hn in
theorem card_cornerCutEdges : (cornerCutEdges n).card = 4 := by
  classical
  rw [cornerCutEdges, Finset.card_image_of_injective _ (cornerCutEdge_injective n hn)]
  decide

theorem cornerCutEdge_ne_ghostOutwardEdge
    (x : BoundaryVertex (box n)) : cornerCutEdge n b ≠ ghostOutwardEdge n x := by
  intro h
  have he : s(cornerPoint n b, cornerOutwardPoint n b) =
      s(x.val.val, ghostOutwardNeighbor x) :=
    congrArg (fun e : OuterBoxEdge n => Sym2.map Subtype.val e.val) h
  grind [cornerOutwardPoint, cornerPoint, ghostOutwardNeighbor]

/-- The event used in the outer wired conditioning, for positive inner radius. -/
def cornerClosureEvent : Set (FK.Configuration
    (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ)))) :=
  allClosedEdges (cornerCutEdges n)

include hn in
/-- The exact four-corner event has the uniform finite-energy lower bound. -/
theorem cornerClosureEvent_probability_lower_bound :
    (1 - FK.edgeParameter q) ^ 4 ≤
      (FK.measure (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ))) q
        (FK.BoundaryCondition.wired {x | x.val ∈ vertexBoundary (box (n + 1))})
        (cornerClosureEvent n)).toReal := by
  have h := measure_allClosedEdges_lower_bound q
    (FK.BoundaryCondition.wired {x | x.val ∈ vertexBoundary (box (n + 1))}) (cornerCutEdges n)
  rw [card_cornerCutEdges n hn] at h
  exact h

end
end PottsDiscontinuity.Potts
