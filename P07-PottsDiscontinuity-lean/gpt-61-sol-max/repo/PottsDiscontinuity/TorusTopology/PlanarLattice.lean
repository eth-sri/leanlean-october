/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Interval

/-! The square lattice and its finite closed boxes.

The vertex carrier of each induced graph is the entire box, including isolated
vertices. These boxes are lattice infrastructure, not a definition of the marked
Jordan-domain approximations in Theorem 1.1.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar

/-- Vertices of the unscaled square lattice. -/
abbrev LatticeVertex := ℤ × ℤ

/-- Horizontal or vertical unit-step adjacency on the square lattice. -/
def squareLattice : SimpleGraph LatticeVertex where
  Adj u v :=
     (u.1 + 1 = v.1 ∨ v.1 + 1 = u.1) ∧ u.2 = v.2  ∨
     u.1 = v.1 ∧ (u.2 + 1 = v.2 ∨ v.2 + 1 = u.2) 
  symm := ⟨by intro u v h; omega⟩
  loopless := ⟨by intro u; omega⟩

instance : DecidableRel squareLattice.Adj := by
  intro u v
  unfold squareLattice
  infer_instance

lemma squareLattice_adj_iff (u v : LatticeVertex) :
    squareLattice.Adj u v ↔
       (u.1 + 1 = v.1 ∨ v.1 + 1 = u.1) ∧ u.2 = v.2  ∨
       u.1 = v.1 ∧ (u.2 + 1 = v.2 ∨ v.2 + 1 = u.2)  := Iff.rfl

/-- The closed integer box with center `c` and coordinate radius `r`. -/
def latticeBox (c : LatticeVertex) (r : ℕ) : Finset LatticeVertex :=
   Finset.Icc (c.1 - (r : ℤ)) (c.1 + (r : ℤ))  ×ˢ
     Finset.Icc (c.2 - (r : ℤ)) (c.2 + (r : ℤ)) 

lemma mem_latticeBox (c v : LatticeVertex) (r : ℕ) :
    v ∈ latticeBox c r ↔
      (c.1 - (r : ℤ) ≤ v.1 ∧ v.1 ≤ c.1 + (r : ℤ)) ∧
       c.2 - (r : ℤ) ≤ v.2 ∧ v.2 ≤ c.2 + (r : ℤ)  := by
  grind +locals

lemma card_latticeBox (c : LatticeVertex) (r : ℕ) :
    (latticeBox c r).card = (2 * r + 1) ^ 2 := by
  rw [latticeBox, Finset.card_product, Int.card_Icc, Int.card_Icc]
  grind







end PottsDiscontinuity.TorusTopology.Planar
