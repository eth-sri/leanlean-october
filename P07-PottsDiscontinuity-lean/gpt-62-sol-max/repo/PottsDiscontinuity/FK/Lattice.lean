/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.Frozen.Defs.VertexBoundary
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

namespace PottsDiscontinuity.FK

/-- Vertices of the unscaled square lattice. -/
abbrev LatticeVertex := ℤ × ℤ

/-- Horizontal or vertical unit-step adjacency on the square lattice. -/
abbrev squareLattice : SimpleGraph LatticeVertex :=
  PottsDiscontinuity.squareLattice

instance : DecidableRel squareLattice.Adj := by
  intro u v
  unfold squareLattice PottsDiscontinuity.squareLattice
  infer_instance

lemma squareLattice_adj_iff (u v : LatticeVertex) :
    squareLattice.Adj u v ↔
      ((u.1 + 1 = v.1 ∨ v.1 + 1 = u.1) ∧ u.2 = v.2) ∨
      (u.1 = v.1 ∧ (u.2 + 1 = v.2 ∨ v.2 + 1 = u.2)) := by
  change |u.1 - v.1| + |u.2 - v.2| = 1 ↔ _
  simp only [abs_eq_max_neg]
  omega

/-- The boundary of a closed integer rectangle is the union of its four sides. -/
theorem vertexBoundary_rect {V : Finset LatticeVertex} {l r b t : ℤ}
    (hV : ∀ x : LatticeVertex, x ∈ V ↔ (l ≤ x.1 ∧ x.1 ≤ r) ∧ (b ≤ x.2 ∧ x.2 ≤ t))
    (x : LatticeVertex) : x ∈ vertexBoundary V ↔
      x ∈ V ∧ (x.1 = l ∨ x.1 = r ∨ x.2 = b ∨ x.2 = t) := by
  constructor
  · rintro ⟨hx, y, hxy, hy⟩
    have hx' := (hV x).1 hx
    rw [hV] at hy
    rw [squareLattice_adj_iff] at hxy
    exact ⟨hx, by omega⟩
  · rintro ⟨hx, hs⟩
    refine ⟨hx, if x.1 = l then (x.1 - 1, x.2) else if x.1 = r then (x.1 + 1, x.2)
      else if x.2 = b then (x.1, x.2 - 1) else (x.1, x.2 + 1), ?_⟩
    split_ifs <;> constructor <;> first
    | rw [squareLattice_adj_iff]; dsimp; omega
    | rw [hV]; dsimp; omega

/-- Translation by an integer lattice vector. -/
def latticeTranslate (a v : LatticeVertex) : LatticeVertex :=
  (v.1 + a.1, v.2 + a.2)

lemma latticeTranslate_neg_cancel (a v : LatticeVertex) :
    latticeTranslate (-a) (latticeTranslate a v) = v := by
  ext <;> dsimp [latticeTranslate] <;> omega

lemma squareLattice_adj_translate_iff (a u v : LatticeVertex) :
    squareLattice.Adj (latticeTranslate a u) (latticeTranslate a v) ↔
      squareLattice.Adj u v := by
  simp only [squareLattice_adj_iff, latticeTranslate]
  omega

/-- Every integer translation is a graph automorphism of the square lattice. -/
def latticeTranslationIso (a : LatticeVertex) : squareLattice ≃g squareLattice where
  toFun := latticeTranslate a
  invFun := latticeTranslate (-a)
  left_inv := latticeTranslate_neg_cancel a
  right_inv v := by ext <;> dsimp [latticeTranslate] <;> omega
  map_rel_iff' := squareLattice_adj_translate_iff a _ _

/-- The closed integer box with center `c` and coordinate radius `r`. -/
def latticeBox (c : LatticeVertex) (r : ℕ) : Finset LatticeVertex :=
  (Finset.Icc (c.1 - (r : ℤ)) (c.1 + (r : ℤ))) ×ˢ
    (Finset.Icc (c.2 - (r : ℤ)) (c.2 + (r : ℤ)))

lemma mem_latticeBox (c v : LatticeVertex) (r : ℕ) :
    v ∈ latticeBox c r ↔
      (c.1 - (r : ℤ) ≤ v.1 ∧ v.1 ≤ c.1 + (r : ℤ)) ∧
      (c.2 - (r : ℤ) ≤ v.2 ∧ v.2 ≤ c.2 + (r : ℤ)) := by
  simp [latticeBox]

lemma center_mem_latticeBox (c : LatticeVertex) (r : ℕ) : c ∈ latticeBox c r := by
  rw [mem_latticeBox]
  omega

lemma latticeBox_mono (c : LatticeVertex) {r s : ℕ} (hrs : r ≤ s) :
    latticeBox c r ⊆ latticeBox c s := by
  intro v hv
  rw [mem_latticeBox] at hv ⊢
  omega

lemma mem_latticeBox_translate_iff (a c v : LatticeVertex) (r : ℕ) :
    latticeTranslate a v ∈ latticeBox (latticeTranslate a c) r ↔
      v ∈ latticeBox c r := by
  simp only [mem_latticeBox, latticeTranslate]
  omega

/-- All vertices of a finite box, regardless of whether they meet an open edge. -/
abbrev BoxVertex (c : LatticeVertex) (r : ℕ) := {v : LatticeVertex // v ∈ latticeBox c r}

/-- The induced square-lattice graph on the full box carrier. -/
def boxGraph (c : LatticeVertex) (r : ℕ) : SimpleGraph (BoxVertex c r) :=
  squareLattice.induce (latticeBox c r : Set LatticeVertex)

instance (c : LatticeVertex) (r : ℕ) : DecidableRel (boxGraph c r).Adj := by
  unfold boxGraph
  infer_instance

lemma boxGraph_adj_iff (c : LatticeVertex) (r : ℕ) (u v : BoxVertex c r) :
    (boxGraph c r).Adj u v ↔ squareLattice.Adj u.val v.val := Iff.rfl

end PottsDiscontinuity.FK
