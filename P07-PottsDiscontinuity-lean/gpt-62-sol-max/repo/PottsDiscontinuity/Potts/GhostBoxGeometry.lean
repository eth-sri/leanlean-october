module

public import PottsDiscontinuity.Potts.LiteralBoundary
public import PottsDiscontinuity.FK.Lattice
public import PottsDiscontinuity.Frozen.Defs.Box

/-! Exact geometry of one ghost bond per boundary vertex of a square box. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

section

variable (n : ℕ)

theorem mem_box_iff (x : ℤ × ℤ) :
    x ∈ box n ↔ (-(n : ℤ) ≤ x.1 ∧ x.1 ≤ n) ∧ (-(n : ℤ) ≤ x.2 ∧ x.2 ≤ n) := by
  simp [box]

theorem box_subset_box_succ : box n ⊆ box (n + 1) := by
  intro x hx
  rw [mem_box_iff] at hx ⊢
  omega

theorem mem_vertexBoundary_box_iff (x : ℤ × ℤ) :
    x ∈ vertexBoundary (box n) ↔ x ∈ box n ∧
      (x.1 = -(n : ℤ) ∨ x.1 = n ∨ x.2 = -(n : ℤ) ∨ x.2 = n) :=
  FK.vertexBoundary_rect (mem_box_iff n) x

/-- The one-layer shell is exactly the wired boundary of the outer box. -/
theorem outer_shell_iff_boundary (x : ℤ × ℤ) (hx : x ∈ box (n + 1)) :
    x ∉ box n ↔ x ∈ vertexBoundary (box (n + 1)) := by
  rw [mem_vertexBoundary_box_iff, mem_box_iff, mem_box_iff]
  rw [mem_box_iff] at hx
  omega

end

section

variable (n : ℕ) (x : BoundaryVertex (box n))

/-- Retain the horizontal outward edge at corners, and the unique outward edge
at every other boundary vertex. This definition also selects one edge at radius zero. -/
def ghostOutwardNeighbor : ℤ × ℤ :=
  if x.val.val.1 = (n : ℤ) then (n + 1, x.val.val.2)
  else if x.val.val.1 = -(n : ℤ) then (-(n : ℤ) - 1, x.val.val.2)
  else if x.val.val.2 = (n : ℤ) then (x.val.val.1, n + 1)
  else (x.val.val.1, -(n : ℤ) - 1)

theorem ghostOutwardNeighbor_adj :
    squareLattice.Adj x.val.val (ghostOutwardNeighbor n x) := by
  have hb := (mem_vertexBoundary_box_iff n x.val.val).mp x.property
  rw [FK.squareLattice_adj_iff]
  unfold ghostOutwardNeighbor
  split_ifs <;> dsimp <;> omega

theorem ghostOutwardNeighbor_not_mem :
    ghostOutwardNeighbor n x ∉ box n := by
  rw [mem_box_iff]
  unfold ghostOutwardNeighbor
  split_ifs <;> dsimp <;> omega

theorem ghostOutwardNeighbor_mem_outer :
    ghostOutwardNeighbor n x ∈ box (n + 1) := by
  have hx := (mem_box_iff n x.val.val).mp x.val.property
  rw [mem_box_iff]
  unfold ghostOutwardNeighbor
  split_ifs <;> dsimp <;> omega

end

section

variable (n : ℕ)

abbrev OuterBoxEdge :=
  (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ))).edgeSet

/-- The retained outward edge representing the boundary vertex's single ghost bond. -/
def ghostOutwardEdge (x : BoundaryVertex (box n)) : OuterBoxEdge n :=
  ⟨s(⟨x.val.val, box_subset_box_succ n x.val.property⟩,
      ⟨ghostOutwardNeighbor n x, ghostOutwardNeighbor_mem_outer n x⟩),
    (squareLattice.induce _).mem_edgeSet.mpr (ghostOutwardNeighbor_adj n x)⟩

theorem ghostOutwardEdge_injective : Function.Injective (ghostOutwardEdge n) := by
  intro x y h
  have he : s(x.val.val, ghostOutwardNeighbor n x) =
      s(y.val.val, ghostOutwardNeighbor n y) := by
    have hh := congrArg (fun e : OuterBoxEdge n => Sym2.map Subtype.val e.val) h
    exact hh
  rcases Sym2.eq_iff.mp he with ⟨hxy, _⟩ | ⟨hxy, _⟩
  · exact Subtype.ext (Subtype.ext hxy)
  · exact (ghostOutwardNeighbor_not_mem n y (hxy ▸ x.val.property)).elim

/-- Collapse exactly the outer wired boundary to the ghost. -/
def collapseOuterBox (x : ↥(box (n + 1) : Set (ℤ × ℤ))) :
    Option ↥(box n : Set (ℤ × ℤ)) :=
  if hx : x.val ∈ box n then some ⟨x.val, hx⟩ else none

@[simp] theorem collapseOuterBox_inner (x : ↥(box n : Set (ℤ × ℤ))) :
    collapseOuterBox n ⟨x.val, box_subset_box_succ n x.property⟩ = some x := by
  simp [collapseOuterBox]

@[simp] theorem collapseOuterBox_outward (x : BoundaryVertex (box n)) :
    collapseOuterBox n ⟨ghostOutwardNeighbor n x, ghostOutwardNeighbor_mem_outer n x⟩ = none := by
  simp [collapseOuterBox, ghostOutwardNeighbor_not_mem]

theorem collapseOuterBox_eq_none_iff (x : ↥(box (n + 1) : Set (ℤ × ℤ))) :
    collapseOuterBox n x = none ↔ x.val ∈ vertexBoundary (box (n + 1)) := by
  simp only [collapseOuterBox, dite_eq_right_iff, Option.some_ne_none, imp_false]
  exact outer_shell_iff_boundary n x.val x.property

end

end
end PottsDiscontinuity.Potts
