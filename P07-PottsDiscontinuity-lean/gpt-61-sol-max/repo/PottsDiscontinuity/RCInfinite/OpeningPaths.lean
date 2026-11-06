module
public import Mathlib

public import PottsDiscontinuity.RCInfinite.ClusterEvents
public import PottsDiscontinuity.RCInfinite.FiniteModification

@[expose] public section

open Set

namespace PottsDiscontinuity.RCInfinite
open FK
noncomputable section
open scoped Classical

theorem lattice_horizontal_reachable (a b y : ℤ) : squareLattice.Reachable (a, y) (b, y) := by
  have haux (z : ℤ) : squareLattice.Reachable (a, y) (a + z, y) := by
    induction z using Int.induction_on with
    | zero => simp_all
    | succ n ih =>
      exact ih.trans (show squareLattice.Adj (a + n, y) (a + (n + 1), y) from by
        rw [squareLattice_adj_iff]
        omega).reachable
    | pred n ih =>
      exact ih.trans (show squareLattice.Adj (a + -n, y) (a + (-n - 1), y) from by
        rw [squareLattice_adj_iff]
        omega).reachable
  have hab : a + (b - a) = b := by ring
  simpa only [hab] using haux (b - a)

theorem lattice_vertical_reachable (x a b : ℤ) : squareLattice.Reachable (x, a) (x, b) := by
  have haux (z : ℤ) : squareLattice.Reachable (x, a) (x, a + z) := by
    induction z using Int.induction_on with
    | zero => simp_all
    | succ n ih =>
      exact ih.trans (show squareLattice.Adj (x, a + n) (x, a + (n + 1)) from by
        rw [squareLattice_adj_iff]
        omega).reachable
    | pred n ih =>
      exact ih.trans (show squareLattice.Adj (x, a + -n) (x, a + (-n - 1)) from by
        rw [squareLattice_adj_iff]
        omega).reachable
  have hab : a + (b - a) = b := by ring
  simpa only [hab] using haux (b - a)

theorem squareLattice_reachable (x y : LatticeVertex) : squareLattice.Reachable x y :=
  (lattice_horizontal_reachable x.1 y.1 x.2).trans (lattice_vertical_reachable y.1 x.2 y.2)

theorem rcInfiniteOpenGraph_edgeSet (ω : LatticeConfiguration) :
    (rcInfiniteOpenGraph ω).edgeSet = {e | ∃ h : e ∈ squareLattice.edgeSet, ω ⟨e, h⟩ = true} := by
  rw [rcInfiniteOpenGraph, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact And.left
  · rintro ⟨h, hh⟩
    exact ⟨⟨h, hh⟩, squareLattice.not_isDiag_of_mem_edgeSet h⟩

/-- The finite set of original edges traversed by a lattice walk. -/
def latticeWalkEdges {x y : LatticeVertex} (w : squareLattice.Walk x y) : Finset Edge :=
  w.edges.toFinset.attach.map
    { toFun := fun e : ↥w.edges.toFinset => (⟨e.val, w.edges_subset_edgeSet
        (List.mem_toFinset.mp e.property)⟩ : Edge)
      inj' := fun _e _f h => Subtype.ext (congrArg (fun z : Edge => z.val) h) }

section

variable {x y : LatticeVertex} (w : squareLattice.Walk x y)
include w

theorem mem_latticeWalkEdges  (e : Edge) :
    e ∈ latticeWalkEdges w ↔ e.val ∈ w.edges := by
  rw [latticeWalkEdges, Finset.mem_map]
  constructor
  · rintro ⟨f, _, hf⟩
    have hv : f.val = e.val := congrArg Subtype.val hf
    simpa only [hv, List.mem_toFinset] using f.property
  · aesop

theorem opening_walk_reachable 
    (F : Finset Edge) (hF : latticeWalkEdges w ⊆ F) (ω : LatticeConfiguration) :
    (rcInfiniteOpenGraph (setEdges F (fun _ => true) ω)).Reachable x y := by
  apply (w.transfer (rcInfiniteOpenGraph (setEdges F (fun _ => true) ω)) _).reachable
  intro e he
  rw [rcInfiniteOpenGraph_edgeSet]
  have hG := w.edges_subset_edgeSet he
  refine ⟨hG, ?_⟩
  have heF :  ⟨e, hG⟩  ∈ F := by
                                       solve_by_elim [_root_.Iff.mpr, _root_.PottsDiscontinuity.RCInfinite.mem_latticeWalkEdges]
  simp only [setEdges, heF, ite_true]

end

theorem opening_graph_mono (F : Finset Edge) (ω : LatticeConfiguration) :
    rcInfiniteOpenGraph ω ≤ rcInfiniteOpenGraph (setEdges F (fun _ => true) ω) := by
  intro x y hxy
  obtain ⟨he, hω⟩ := (rcInfiniteOpenGraph_adj ω x y).mp hxy
  apply (rcInfiniteOpenGraph_adj _ x y).mpr
  refine ⟨he, ?_⟩
  by_cases hf : (⟨s(x, y), he⟩ ) ∈ F <;> simp [setEdges, hω]

/-- Any prescribed finite family of vertices can be connected by opening a
fixed finite set of lattice edges, independently of the sampled field. -/
theorem exists_finite_opening_connects (n : ℕ) (xs : Fin n → LatticeVertex) :
    ∃ F : Finset Edge, ∀ ω : LatticeConfiguration, ∀ j k : Fin n,
      (rcInfiniteOpenGraph (setEdges F (fun _ => true) ω)).Reachable (xs j) (xs k) := by
  cases n with
  | zero => simp_all
  | succ n =>
    have hwalk (j : Fin (n + 1)) : ∃ w : squareLattice.Walk (xs 0) (xs j), True := Nonempty.casesOn (squareLattice_reachable (xs 0) (xs j)) fun w => Exists.intro w trivial
    choose w _ using hwalk
    let F  := Finset.univ.biUnion fun j => latticeWalkEdges (w j)
    have hsubset (j : Fin (n + 1)) : latticeWalkEdges (w j) ⊆ F := by
      intro e he
      aesop
    refine ⟨F, fun ω j k => ?_⟩
    exact (opening_walk_reachable (w j) F (hsubset j) ω).symm.trans
      (opening_walk_reachable (w k) F (hsubset k) ω)

end
end PottsDiscontinuity.RCInfinite
