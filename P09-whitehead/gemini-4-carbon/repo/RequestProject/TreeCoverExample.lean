module

public import RequestProject.TreeCoverTheoremA

@[expose] public section

/-!
# Non-vacuity of the tree-collapse form of Theorem A

The statement `FiniteChains.Comb.SpanningTree.hasAcyclicRegularCover_of_topChains` is applied
here to a complex whose spanning tree is not trivial: the *interval*, two vertices joined by an
edge.  Its spanning tree consists of that edge, so the collapse is the empty presentation, the
chains of condition (1) exist in every length (take all of them empty), and the theorem yields
a connected acyclic regular cover of the interval.
-/

namespace FiniteChains
namespace Comb
namespace SpanningTree

universe u

/-- The interval: two vertices, one edge, no two-cells. -/
def intervalComplex : Complex2.{u} where
  V := ULift.{u} Bool
  E := PUnit.{u + 1}
  F := PEmpty.{u + 1}
  src _ := ULift.up false
  tgt _ := ULift.up true
  base := PEmpty.elim
  att := PEmpty.elim
  att_isLoop := fun f => f.elim

/-- The spanning tree of the interval: its only edge. -/
def intervalTree : SpanningTree intervalComplex.{u} where
  root := ULift.up false
  ht a := if a.down then 1 else 0
  isTree _ := True
  up a _ := (PUnit.unit, false)
  ht_root := rfl
  ht_eq_zero := by
    rintro ⟨a⟩ ha
    cases a
    · rfl
    · simp at ha
  up_src := by
    rintro ⟨a⟩ ha
    cases a
    · exact absurd rfl ha
    · rfl
  up_ht := by
    rintro ⟨a⟩ ha
    cases a
    · exact absurd rfl ha
    · rfl
  isTree_iff := fun _ =>
    ⟨fun _ => ⟨ULift.up true, by intro h; exact Bool.noConfusion (congrArg ULift.down h), rfl⟩,
      fun _ => trivial⟩

instance : IsEmpty (NonTree intervalTree.{u}) := ⟨fun x => x.2 trivial⟩

instance : Fintype intervalComplex.{u}.F := inferInstanceAs (Fintype PEmpty.{u + 1})

instance : DecidableEq intervalComplex.{u}.F := inferInstanceAs (DecidableEq PEmpty.{u + 1})

noncomputable instance : Fintype (NonTree intervalTree.{u}) := Fintype.ofIsEmpty

instance : DecidableEq (NonTree intervalTree.{u}) := fun x => isEmptyElim x

end SpanningTree
end Comb
end FiniteChains
