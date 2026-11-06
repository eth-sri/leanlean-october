module

public import PottsDiscontinuity.Potts.GhostBoxGeometry
public import PottsDiscontinuity.Potts.FiniteEnergyBounds

/-! The four corner edges omitted by the literal boundary term. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

section
variable (n : ℕ) (b : Bool × Bool)
def cornerPoint : ℤ × ℤ :=
  (if b.1 then (n : ℤ) else -(n : ℤ), if b.2 then (n : ℤ) else -(n : ℤ))

def cornerOutwardPoint : ℤ × ℤ :=
  ((cornerPoint n b).1, if b.2 then (n : ℤ) + 1 else -(n : ℤ) - 1)

theorem cornerPoint_mem : cornerPoint n b ∈ box n := by
  rcases b with ⟨b, c⟩
  cases b <;> cases c <;> rw [mem_box_iff] <;> dsimp [cornerPoint] <;> omega

theorem cornerOutwardPoint_mem :
    cornerOutwardPoint n b ∈ box (n + 1) := by
  rcases b with ⟨b, c⟩
  cases b <;> cases c <;> rw [mem_box_iff] <;>
    dsimp [cornerOutwardPoint, cornerPoint] <;> omega

theorem cornerOutwardPoint_not_mem :
    cornerOutwardPoint n b ∉ box n := by
  rcases b with ⟨b, c⟩
  cases b <;> cases c <;> rw [mem_box_iff] <;>
    dsimp [cornerOutwardPoint, cornerPoint] <;> omega

theorem cornerPoint_adj_outward :
    squareLattice.Adj (cornerPoint n b) (cornerOutwardPoint n b) := by
  rcases b with ⟨b, c⟩
  cases b <;> cases c <;> rw [FK.squareLattice_adj_iff] <;>
    dsimp [cornerOutwardPoint, cornerPoint] <;> omega

/-- The vertical outward edge at a corner; the horizontal one is retained. -/
def cornerCutEdge : OuterBoxEdge n :=
  ⟨s(⟨cornerPoint n b, box_subset_box_succ n (cornerPoint_mem n b)⟩,
      ⟨cornerOutwardPoint n b, cornerOutwardPoint_mem n b⟩),
    (squareLattice.induce _).mem_edgeSet.mpr (cornerPoint_adj_outward n b)⟩
end

section
variable (n : ℕ)
include n
theorem cornerPoint_injective (hn : 0 < n) : Function.Injective (cornerPoint n) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  grind [cornerPoint]

theorem cornerCutEdge_injective (hn : 0 < n) : Function.Injective (cornerCutEdge n) := by
  intro b c h
  have he : s(cornerPoint n b, cornerOutwardPoint n b) =
      s(cornerPoint n c, cornerOutwardPoint n c) :=
    congrArg (fun e : OuterBoxEdge n => Sym2.map Subtype.val e.val) h
  rcases Sym2.eq_iff.mp he with ⟨hbc, _⟩ | ⟨hbc, _⟩
  · grind [cornerPoint_injective]
  · exact (cornerOutwardPoint_not_mem n c (hbc ▸ cornerPoint_mem n b)).elim

def cornerCutEdges  : Finset (OuterBoxEdge n) := by
  classical
  exact Finset.univ.image (cornerCutEdge n)

theorem card_cornerCutEdges (hn : 0 < n) : (cornerCutEdges n).card = 4 := by
  rw [cornerCutEdges, Finset.card_image_of_injective _ (cornerCutEdge_injective n hn)]
  decide

theorem cornerCutEdge_ne_ghostOutwardEdge (b : Bool × Bool)
    (x : BoundaryVertex (box n)) : cornerCutEdge n b ≠ ghostOutwardEdge n x := by
  intro h
  have he : s(cornerPoint n b, cornerOutwardPoint n b) =
      s(x.val.val, ghostOutwardNeighbor n x) :=
    congrArg (fun e : OuterBoxEdge n => Sym2.map Subtype.val e.val) h
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, _⟩
  · grind [cornerOutwardPoint, cornerPoint, ghostOutwardNeighbor]
  · exact (ghostOutwardNeighbor_not_mem n x (h1 ▸ cornerPoint_mem n b)).elim

/-- The event used in the outer wired conditioning, for positive inner radius. -/
def cornerClosureEvent  : Set (FK.Configuration
    (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ)))) :=
  allClosedEdges (cornerCutEdges n)
end

/-- The exact four-corner event has the uniform finite-energy lower bound. -/
theorem cornerClosureEvent_probability_lower_bound (q : FK.Parameters) (n : ℕ) (hn : 0 < n) :
    (1 - FK.edgeParameter q) ^ 4 ≤
      (FK.measure (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ))) q
        (FK.BoundaryCondition.wired {x | x.val ∈ vertexBoundary (box (n + 1))})
        (cornerClosureEvent n)).toReal := by
  have h := measure_allClosedEdges_lower_bound q
    (FK.BoundaryCondition.wired {x | x.val ∈ vertexBoundary (box (n + 1))}) (cornerCutEdges n)
  rw [card_cornerCutEdges n hn] at h
  tauto

end
end PottsDiscontinuity.Potts
