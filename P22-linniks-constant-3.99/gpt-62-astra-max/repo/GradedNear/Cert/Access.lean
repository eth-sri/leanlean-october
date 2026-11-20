module

public import GradedNear.Defs

/-! # Accessing and scaling the coordinates of a leaf row -/

@[expose] public section
namespace GradedNear.Cert

abbrev Leaf.row (L : Leaf) (k : ℕ) := rowAt L k
abbrev Leaf.feature (L : Leaf) (j : Fin L.cols.length) (k : ℕ) := featureAt (L.cols.get j) k
abbrev Leaf.diag (L : Leaf) (j : Fin L.cols.length) (k : ℕ) := diagonalAt (L.cols.get j) k
abbrev Leaf.family (L : Leaf) (k : ℕ) (i : Fin (L.row k).fam.length) := (L.row k).fam.get i
noncomputable abbrev scaled (v : ℤ) := inUnits v

end GradedNear.Cert
