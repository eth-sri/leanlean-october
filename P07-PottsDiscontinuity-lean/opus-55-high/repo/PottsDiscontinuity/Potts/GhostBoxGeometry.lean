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

theorem box_subset_box_succ  : box n ⊆ box (n + 1) := by
  grind [mem_box_iff]

theorem mem_vertexBoundary_box_iff (x : ℤ × ℤ) :
    x ∈ vertexBoundary (box n) ↔ x ∈ box n ∧
      (x.1 = -(n : ℤ) ∨ x.1 = n ∨ x.2 = -(n : ℤ) ∨ x.2 = n) := by
  constructor
  · rintro ⟨hx, y, hxy, hy⟩
    rw [FK.squareLattice_adj_iff] at hxy
    grind [mem_box_iff]
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    rcases h with h | h | h | h
    · refine ⟨(x.1 - 1, x.2), ?_, ?_⟩
      · rw [FK.squareLattice_adj_iff]; omega
      simp_all [mem_box_iff]
    · refine ⟨(x.1 + 1, x.2), ?_, ?_⟩
      · rw [FK.squareLattice_adj_iff]; omega
      simp_all [mem_box_iff]
    · refine ⟨(x.1, x.2 - 1), ?_, ?_⟩
      · rw [FK.squareLattice_adj_iff]; omega
      simp_all [mem_box_iff]
    · refine ⟨(x.1, x.2 + 1), ?_, ?_⟩
      · rw [FK.squareLattice_adj_iff]; omega
      simp_all [mem_box_iff]

/-- The one-layer shell is exactly the wired boundary of the outer box. -/
theorem outer_shell_iff_boundary (x : ℤ × ℤ) (hx : x ∈ box (n + 1)) :
    x ∉ box n ↔ x ∈ vertexBoundary (box (n + 1)) := by
  grind [mem_vertexBoundary_box_iff, mem_box_iff]

/-- Retain the horizontal outward edge at corners, and the unique outward edge
at every other boundary vertex. This definition also selects one edge at radius zero. -/
def ghostOutwardNeighbor (x : BoundaryVertex (box n)) : ℤ × ℤ :=
  if x.val.val.1 = (n : ℤ) then (n + 1, x.val.val.2)
  else if x.val.val.1 = -(n : ℤ) then (-(n : ℤ) - 1, x.val.val.2)
  else if x.val.val.2 = (n : ℤ) then (x.val.val.1, n + 1)
  else (x.val.val.1, -(n : ℤ) - 1)
end

section
variable (n : ℕ) (x : BoundaryVertex (box n))
theorem ghostOutwardNeighbor_adj  :
    squareLattice.Adj x.val.val (ghostOutwardNeighbor n x) := by
  have hb := (mem_vertexBoundary_box_iff n x.val.val).mp x.property
  rw [FK.squareLattice_adj_iff]
  grind [ghostOutwardNeighbor]

theorem ghostOutwardNeighbor_not_mem  :
    ghostOutwardNeighbor n x ∉ box n := by
  grind [mem_box_iff, ghostOutwardNeighbor]

theorem ghostOutwardNeighbor_mem_outer  :
    ghostOutwardNeighbor n x ∈ box (n + 1) := by
  grind [mem_box_iff, ghostOutwardNeighbor]
end

section
variable (n : ℕ)
abbrev OuterBoxEdge  :=
  (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ))).edgeSet

/-- The retained outward edge representing the boundary vertex's single ghost bond. -/
def ghostOutwardEdge (x : BoundaryVertex (box n)) : OuterBoxEdge n :=
  ⟨s(⟨x.val.val, box_subset_box_succ n x.val.property⟩,
      ⟨ghostOutwardNeighbor n x, ghostOutwardNeighbor_mem_outer n x⟩),
    (squareLattice.induce _).mem_edgeSet.mpr (ghostOutwardNeighbor_adj n x)⟩

theorem ghostOutwardEdge_injective  : Function.Injective (ghostOutwardEdge n) := by
  intro x y h
  have he : s(x.val.val, ghostOutwardNeighbor n x) =
      s(y.val.val, ghostOutwardNeighbor n y) := by
    have hh := congrArg (fun e : OuterBoxEdge n => Sym2.map Subtype.val e.val) h
    tauto
  grind [ghostOutwardNeighbor_not_mem]

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
  simp [collapseOuterBox, outer_shell_iff_boundary]
end

end
end PottsDiscontinuity.Potts
