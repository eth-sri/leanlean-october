module


public import RequestProject.PresRoseAffineWordReading
public import Mathlib.GroupTheory.FreeGroup.Reduce

@[expose] public section

/-! Free reduction and insertion of a cancelling pair give actual based
path homotopies in the literal disk rose, and hence actual homotopies of
disk attaching maps. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology

namespace FiniteChains.PresModel
open ClassicalGraphModel RelativeAttachment

variable {A : Type}

theorem classicalRoseRead_append (l m : List (A × Bool)) :
    ((classicalRoseRead l).trans (classicalRoseRead m)).Homotopic (classicalRoseRead (l ++ m)) := by
  induction l with
  | nil => exact Path.Homotopic.refl_trans _
  | cons p l ih =>
    exact (Path.Homotopic.trans_assoc _ _ _).trans ((Path.Homotopic.refl _).hcomp ih)

theorem classicalRoseRead_cancelHead (a : A) (b : Bool) (l : List _) :
    (classicalRoseRead ((a, b) :: (a, !b) :: l)).Homotopic (classicalRoseRead l) := by
  cases b
  · exact (Path.Homotopic.trans_assoc _ _ _).symm.trans
      (((Path.Homotopic.symm_trans _).hcomp (Path.Homotopic.refl _)).trans
        (Path.Homotopic.refl_trans _))
  · exact (Path.Homotopic.trans_assoc _ _ _).symm.trans
      (((Path.Homotopic.trans_symm _).hcomp (Path.Homotopic.refl _)).trans
        (Path.Homotopic.refl_trans _))

theorem classicalRoseRead_cancelPair (l r : List _) (a : A) (b : Bool) :
    (classicalRoseRead (l ++ (a, b) :: (a, !b) :: r)).Homotopic (classicalRoseRead (l ++ r)) :=
  (classicalRoseRead_append l _).symm.trans
    (((Path.Homotopic.refl _).hcomp (classicalRoseRead_cancelHead a b r)).trans
      (classicalRoseRead_append l r))

variable {l m : List (A × Bool)}

theorem classicalRoseRead_homotopic_of_step (h : FreeGroup.Red.Step l m) :
    (classicalRoseRead l).Homotopic (classicalRoseRead m) := by
  cases h with
  | not => apply classicalRoseRead_cancelPair

theorem classicalRoseRead_homotopic_of_red (h : FreeGroup.Red l m) :
    (classicalRoseRead l).Homotopic (classicalRoseRead m) := by
  induction h with
  | refl => exact Path.Homotopic.refl _
  | tail _ hstep ih => exact ih.trans (classicalRoseRead_homotopic_of_step hstep)

/-- Equality in the free group is realized by an actual fixed-endpoint
homotopy of the continuous word paths. -/
theorem classicalRoseRead_homotopic_of_mk_eq
    (h : FreeGroup.mk l = FreeGroup.mk m) :
    (classicalRoseRead l).Homotopic (classicalRoseRead m) := by
  obtain ⟨r, hl, hm⟩ := FreeGroup.Red.exact.mp h
  exact (classicalRoseRead_homotopic_of_red hl).trans (classicalRoseRead_homotopic_of_red hm).symm

def classicalRoseWordBoundary (l : List (A × Bool)) :=
  (squareLoopDesc (classicalRoseRead l)).comp unitBoundarySquareHomeomorph.toContinuousMap

variable {l m : List (A × Bool)}

theorem classicalRoseWordBoundary_homotopic_of_read
    (h : (classicalRoseRead l).Homotopic (classicalRoseRead m)) :
    (classicalRoseWordBoundary l).Homotopic (classicalRoseWordBoundary m) :=
  (squareLoopDesc_homotopic h).comp
    (ContinuousMap.Homotopic.refl unitBoundarySquareHomeomorph.toContinuousMap)

theorem classicalRoseWordBoundary_homotopic_of_mk_eq
    (h : FreeGroup.mk l = FreeGroup.mk m) :
    (classicalRoseWordBoundary l).Homotopic (classicalRoseWordBoundary m) :=
  classicalRoseWordBoundary_homotopic_of_read (classicalRoseRead_homotopic_of_mk_eq h)

end FiniteChains.PresModel
