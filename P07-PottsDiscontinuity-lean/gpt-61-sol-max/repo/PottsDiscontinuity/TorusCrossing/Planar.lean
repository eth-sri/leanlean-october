module
public import Mathlib

public import PottsDiscontinuity.TorusCrossing.EndGraph

/-!
# Rectangular boards of the rotated lattice, with their primal and dual graphs

`Rect` is a block of cells `[x0, x0 + w] × [y0, y0 + h]`.  Its primal graph has the primal cells
as vertices and one edge for every medial vertex of the *inner* index set
`[x0+1, x0+w] × [y0+1, y0+h]` (the unit squares of the board).  The dual graph has the odd
cells as vertices and the crossing dual edges.  The boundary condition `sepBC` wires the
primal cells of the bottom row together and, separately, those of the top row; `dualBC` wires
the odd cells of the left and right columns into one class.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity

/-- A rectangular board of cells. -/
structure Rect where
  x0 : ℤ
  y0 : ℤ
  w : ℕ
  h : ℕ

namespace Rect

variable (R : Rect)

/-- All cells of the board. -/
def cells : Finset Cell := Finset.Icc R.x0 (R.x0 + R.w) ×ˢ Finset.Icc R.y0 (R.y0 + R.h)

/-- Medial vertices (unit squares) of the board. -/
def inner : Finset Cell := Finset.Icc (R.x0 + 1) (R.x0 + R.w) ×ˢ Finset.Icc (R.y0 + 1) (R.y0 + R.h)

/-- Primal cells of the board. -/
def pcells  := R.cells.filter  IsPrimal 

/-- Odd (dual) cells of the board. -/
def dcells  := R.cells.filter  fun c => ¬ IsPrimal c 

variable {R}

theorem mem_cells {c : Cell} :
    c ∈ R.cells ↔ R.x0 ≤ c.1 ∧ c.1 ≤ R.x0 + R.w ∧ R.y0 ≤ c.2 ∧ c.2 ≤ R.y0 + R.h := by
  grind +locals

theorem mem_inner {m : Cell} :
    m ∈ R.inner ↔ R.x0 + 1 ≤ m.1 ∧ m.1 ≤ R.x0 + R.w ∧ R.y0 + 1 ≤ m.2 ∧ m.2 ≤ R.y0 + R.h := by
  grind +locals

theorem mem_pcells {c : Cell} : c ∈ R.pcells ↔ c ∈ R.cells ∧ IsPrimal c := by
  unfold pcells; simp 

theorem mem_dcells {c : Cell} : c ∈ R.dcells ↔ c ∈ R.cells ∧ ¬ IsPrimal c := by
  unfold dcells; simp 

theorem pData (R : Rect) : EndData primalEnds R.pcells R.inner where
  mem m hm := by
    rw [mem_inner] at hm
    refine ⟨mem_pcells.2 ⟨mem_cells.2 ?_, primalEnds_fst_primal m⟩,
      mem_pcells.2 ⟨mem_cells.2 ?_, primalEnds_snd_primal m⟩⟩ <;>
    · grind [primalEnds]
  ne := primalEnds_ne
  inj _ _ h := primalEnds_inj h

theorem dData (R : Rect) : EndData dualEnds R.dcells R.inner where
  mem m hm := by
    rw [mem_inner] at hm
    refine ⟨mem_dcells.2 ⟨mem_cells.2 ?_, dualEnds_fst_not_primal m⟩,
      mem_dcells.2 ⟨mem_cells.2 ?_, dualEnds_snd_not_primal m⟩⟩ <;>
    · grind [dualEnds]
  ne := dualEnds_ne
  inj _ _ h := dualEnds_inj h

variable (R)

/-- The primal board graph. -/
abbrev pG  := endGraph primalEnds R.pcells R.inner

/-- The dual board graph. -/
abbrev dG  := endGraph dualEnds R.dcells R.inner

/-- Wiring of the bottom row of primal cells and, separately, of the top row. -/
def sepRel (a b : R.pcells)  :=
  a = b ∨  a.1.2 = R.y0 ∧ b.1.2 = R.y0  ∨  a.1.2 = R.y0 + R.h ∧ b.1.2 = R.y0 + R.h 

/-- Boundary condition with the bottom row and top row wired separately. -/
def sepBC : FK.BoundaryCondition R.pcells where
  boundary := {c | c.1.2 = R.y0 ∨ c.1.2 = R.y0 + R.h}
  partition :=
    { r := R.sepRel
      iseqv :=
        { refl := fun a => Or.inl rfl
          symm := by
            grind +locals
          trans := by
            grind +locals }}
  supported := by
    grind +locals

end Rect

end PottsDiscontinuity.TorusCrossing
