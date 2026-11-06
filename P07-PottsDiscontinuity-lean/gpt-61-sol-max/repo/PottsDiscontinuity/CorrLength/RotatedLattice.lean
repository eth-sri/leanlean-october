module

public import Mathlib
public import PottsDiscontinuity.FK.Lattice
public import PottsDiscontinuity.Frozen.Defs.DiagonalSite

/-!
# The rotated lattice and its square-lattice coordinates

The carrier `rotatedVertex` is the even-coordinate-sum sublattice of `ℤ²`.
The map to square-lattice coordinates sends `(i,j)` to
`((i+j)/2, (j-i)/2)`.
-/

@[expose] public section

namespace PottsDiscontinuity.CorrLength

private theorem int_abs_eq_one_iff (z : ℤ) : |z| = 1 ↔ z = 1 ∨ z = -1 := by
                                                                           grind

/-- Vertices of the rotated lattice: pairs of integers with even sum. -/
abbrev RotatedVertex := {z : ℤ × ℤ // Even (z.1 + z.2)}

/-- The rotated-lattice coordinates of a square-lattice vertex. -/
def squareToRotatedVertex (x : ℤ × ℤ) : RotatedVertex :=
  ⟨(x.1 - x.2, x.1 + x.2), ⟨x.1, by simp⟩⟩

/-- The square-lattice coordinates of a rotated-lattice vertex. -/
def rotatedToSquareVertex (x : RotatedVertex) : ℤ × ℤ :=
  ((x.1.1 + x.1.2) / 2, (x.1.2 - x.1.1) / 2)

@[simp] theorem rotatedToSquare_squareToRotated (x : ℤ × ℤ) :
    rotatedToSquareVertex (squareToRotatedVertex x) = x := by
  grind +locals

theorem squareToRotated_rotatedToSquare (x : RotatedVertex) :
    squareToRotatedVertex (rotatedToSquareVertex x) = x := by
  grind +locals

/-- The vertex bijection from the rotated lattice to `ℤ²`. -/
def rotatedVertexEquiv : RotatedVertex ≃ ℤ × ℤ where
  toFun := rotatedToSquareVertex
  invFun := squareToRotatedVertex
  left_inv := squareToRotated_rotatedToSquare
  right_inv := rotatedToSquare_squareToRotated

/-- The rotated lattice with diagonal unit steps. -/
def rotatedLattice : SimpleGraph RotatedVertex :=
  { Adj := fun (x y : RotatedVertex) => |x.1.1 - y.1.1| = 1 ∧ |x.1.2 - y.1.2| = 1
    symm.symm x y h := by
      grind
    loopless.irrefl x h := by
      simp_all }

theorem rotatedLattice_adj_iff_square (x y : RotatedVertex) :
    rotatedLattice.Adj x y ↔
      PottsDiscontinuity.FK.squareLattice.Adj
        (rotatedToSquareVertex x) (rotatedToSquareVertex y) := by
  
  
  rw [PottsDiscontinuity.FK.squareLattice_adj_iff]
  let a := rotatedToSquareVertex x
  let b := rotatedToSquareVertex y
  have hx : (x.1.1, x.1.2) = (a.1 - a.2, a.1 + a.2) := by
    grind +locals
  have hy : (y.1.1, y.1.2) = (b.1 - b.2, b.1 + b.2) := by
    grind +locals
  
  
  
  
  change
     |x.1.1 - y.1.1| = 1 ∧ |x.1.2 - y.1.2| = 1  ↔
        (a.1 + 1 = b.1 ∨ b.1 + 1 = a.1) ∧ a.2 = b.2  ∨
         a.1 = b.1 ∧ (a.2 + 1 = b.2 ∨ b.2 + 1 = a.2)  
  rw [ congrArg Prod.fst hx ,  congrArg Prod.snd hx ,  congrArg Prod.fst hy ,  congrArg Prod.snd hy ]
  rw [int_abs_eq_one_iff, int_abs_eq_one_iff]
  omega

/-- The graph isomorphism from the rotated lattice to the square lattice. -/
def rotatedLatticeIso : rotatedLattice ≃g PottsDiscontinuity.FK.squareLattice where
  toEquiv := rotatedVertexEquiv
  map_rel_iff' := fun {x y} => Iff.symm (rotatedLattice_adj_iff_square x y)

@[simp] theorem diagonalSite_even (m : ℕ) :
    PottsDiscontinuity.diagonalSite (2 * m) = ((m : ℤ), (m : ℤ)) := by
  simp [PottsDiscontinuity.diagonalSite]

@[simp] theorem diagonalSite_odd (m : ℕ) :
    PottsDiscontinuity.diagonalSite (2 * m + 1) = ((m : ℤ), (m : ℤ)) := by
  simp [PottsDiscontinuity.diagonalSite]
  omega

@[simp] theorem rotatedVertexEquiv_apply_origin_to_even_site (m : ℕ) :
    rotatedVertexEquiv ⟨(0, 2 * (m : ℤ)), ⟨(m : ℤ), by ring⟩⟩ =
      ((m : ℤ), (m : ℤ)) := by
  simp [rotatedVertexEquiv, rotatedToSquareVertex]

end PottsDiscontinuity.CorrLength
