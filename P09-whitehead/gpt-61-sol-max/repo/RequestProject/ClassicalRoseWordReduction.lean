import Mathlib.Tactic

import RequestProject.HomeomorphContinuousMap
import RequestProject.PresRoseAffineWordReading
import RequestProject.SquareBoundaryLoopQuotient
import Mathlib.GroupTheory.FreeGroup.Reduce

/-! Free reduction and insertion of a cancelling pair give actual based
path homotopies in the literal disk rose, and hence actual homotopies of
disk attaching maps. Pending Lean verification. -/

noncomputable section


namespace FiniteChains.PresModel
open ClassicalGraphModel RelativeAttachment

variable {A : Type}

theorem classicalRoseRead_append (l m : List (A × Bool)) :
    ((classicalRoseRead l).trans (classicalRoseRead m)).Homotopic (classicalRoseRead (l ++ m)) := by
  induction l with
  | nil => exact Path.Homotopic.refl_trans _
  | cons p l ih =>
    rcases p with ⟨a, b⟩
    exact (Path.Homotopic.trans_assoc _ _ _).trans ((Path.Homotopic.refl _).hcomp ih)

theorem classicalRoseRead_cancelHead (a : A) (b : Bool) (l : List (A × Bool)) :
    (classicalRoseRead ((a, b) :: (a, !b) :: l)).Homotopic (classicalRoseRead l) := by
  cases b
  · change (((graphEdgePath (roseAttaching A) a).symm).trans
      ((graphEdgePath (roseAttaching A) a).trans (classicalRoseRead l))).Homotopic _
    exact (Path.Homotopic.trans_assoc _ _ _).symm.trans
      (((Path.Homotopic.symm_trans _).hcomp (Path.Homotopic.refl _)).trans
        (Path.Homotopic.refl_trans _))
  · change ((graphEdgePath (roseAttaching A) a).trans
      (((graphEdgePath (roseAttaching A) a).symm).trans (classicalRoseRead l))).Homotopic _
    exact (Path.Homotopic.trans_assoc _ _ _).symm.trans
      (((Path.Homotopic.trans_symm _).hcomp (Path.Homotopic.refl _)).trans
        (Path.Homotopic.refl_trans _))

abbrev classicalRoseRead_cancelPair (l r : List (A × Bool)) (a : A) (b : Bool)  :=
  (classicalRoseRead_append l _).symm.trans
    (((Path.Homotopic.refl _).hcomp (classicalRoseRead_cancelHead a b r)).trans
      (classicalRoseRead_append l r))

variable {l m : List (A × Bool)}
theorem classicalRoseRead_homotopic_of_step  (h : FreeGroup.Red.Step l m) :
    (classicalRoseRead l).Homotopic (classicalRoseRead m) := by
  cases h <;> simp_all [classicalRoseRead_cancelPair]

theorem classicalRoseRead_homotopic_of_red  (h : FreeGroup.Red l m) :
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

def classicalRoseWordBoundary (l : List (A × Bool))  :=
  (squareLoopDesc (classicalRoseRead l)).comp unitBoundarySquareHomeomorph.toContinuousMap

abbrev classicalRoseWordBoundary_homotopic_of_read 
    (h : (classicalRoseRead l).Homotopic (classicalRoseRead m))  :=
  ContinuousMap.Homotopic.comp (FiniteChains.RelativeAttachment.squareLoopDesc_homotopic h)
    (ContinuousMap.Homotopic.refl FiniteChains.RelativeAttachment.unitBoundarySquareHomeomorph.toContinuousMap)

abbrev classicalRoseWordBoundary_homotopic_of_mk_eq 
    (h : FreeGroup.mk l = FreeGroup.mk m)  :=
  FiniteChains.PresModel.classicalRoseWordBoundary_homotopic_of_read
    (FiniteChains.PresModel.classicalRoseRead_homotopic_of_mk_eq h)

end FiniteChains.PresModel
