module

public import Mathlib

@[expose] public section

/-!
# Abstract simplicial complexes, flagness, and barycentric subdivisions

Section 3.3 of the paper uses the cubical curvature criterion: a cube complex all of whose
vertex links are *flag* simplicial complexes has a CAT(0) universal cover.  Two purely
combinatorial claims enter the verification of that hypothesis for the complexes `C(L_q)`:

* the barycentric subdivision of a simplicial complex is flag
  ("It is flag: pairwise comparable faces form a chain");
* a disjoint union of flag complexes is flag (used in Step 2 of the proof of the generation
  lemma, where the link of a new vertex is a disjoint union of covers of `L_q`).

Both are proved here for abstract simplicial complexes in the usual combinatorial sense.
The barycentric subdivision is realized, as usual, as the order complex (the complex of
finite chains) of the poset of nonempty faces.
-/

namespace FiniteChains


variable {V : Type u}

/-- An abstract simplicial complex on the vertex type `V`: a downward closed family of
finite subsets of `V` containing the empty face. -/
structure ASC (V : Type u) where
  /-- The family of faces. -/
  faces : Set (Finset V)
  /-- The empty simplex is a face. -/
  empty_mem : (∅ : Finset V) ∈ faces
  /-- Faces are closed under passing to subsets. -/
  down_closed : ∀ {s t : Finset V}, s ∈ faces → t ⊆ s → t ∈ faces

namespace ASC

/-- The order complex of a preorder: its faces are the finite chains. -/
def orderComplex (P : Type u) [Preorder P] : ASC P where
  faces := {s : Finset P | IsChain (· ≤ ·) (s : Set P)}
  empty_mem := by simp [IsChain, Set.Pairwise]
  down_closed := by
    intro s t hs hts
    exact hs.mono (by exact_mod_cast hts)

@[simp] theorem mem_orderComplex {P : Type u} [Preorder P] {s : Finset P} :
    s ∈ (orderComplex P).faces ↔ IsChain (· ≤ ·) (s : Set P) := Iff.rfl

/-- The poset of nonempty faces of `K`, ordered by inclusion. -/
def Face (K : ASC V) : Type u := {s : Finset V // s ∈ K.faces ∧ s.Nonempty}

instance (K : ASC V) : Preorder K.Face := Subtype.preorder _

end ASC

end FiniteChains
