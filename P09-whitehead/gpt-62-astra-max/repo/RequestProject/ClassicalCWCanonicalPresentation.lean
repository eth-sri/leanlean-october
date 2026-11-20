module


public import RequestProject.ClassicalCWWordDiskModel
public import RequestProject.ClassicalRoseWordNaturality
public import RequestProject.PresCircleWordParametrization
public import RequestProject.PresCanonicalWords
public import RequestProject.StabilizedDiskPresentation

@[expose] public section

/-! Every original connected two-dimensional CW complex has an actual
homotopy equivalence to the canonical nonempty-word presentation model.
The generators are its non-tree edges plus one fresh filled circle; the
relators are its original two-cells plus the filling of that circle.
No finite-cell or acyclicity assumption is used. Pending verification. -/

noncomputable section
open scoped Classical unitInterval Topology
namespace FiniteChains.ClassicalCW
open RelativeAttachment ClassicalGraphModel PresModel

variable (K : Whitehead.TwoComplex)

abbrev CanonicalGen := OriginalRoseGen K ⊕ PUnit
abbrev CanonicalRel := OriginalRoseRel K ⊕ PUnit

def canonicalDummy : CanonicalGen K := Sum.inr PUnit.unit

def canonicalRelators : CanonicalRel K → FreeGroup (CanonicalGen K)
  | Sum.inl j => FreeGroup.map Sum.inl (originalRelators K j)
  | Sum.inr _ => FreeGroup.of (canonicalDummy K)

/-- This is literally the selector used by the presentation-chain
construction, including its final cancelling pair. -/
def canonicalWords :=
  presCanonicalWords (canonicalRelators K) (canonicalDummy K)

variable (j : CanonicalRel K)

theorem canonicalWords_ne_nil : canonicalWords K j ≠ [] :=
  presCanonicalWords_ne_nil (canonicalRelators K) (canonicalDummy K) j

theorem canonicalWords_mk :
    FreeGroup.mk (canonicalWords K j) = canonicalRelators K j :=
  mk_presCanonicalWords (canonicalRelators K) (canonicalDummy K) j

def stabilizedOriginalCellBoundary :=
  (StabilizedDiskPresentation.attaching (originalRoseWordAttaching K)).comp
    ⟨Sigma.mk (β := fun _ : CanonicalRel K => UnitBoundary (Fin 2 → ℝ)) j,
      continuous_sigmaMk⟩

theorem stabilizedOriginalCellBoundary_old (j : OriginalRoseRel K) :
    (stabilizedOriginalCellBoundary K (Sum.inl j)).Homotopic
      (classicalPresCellBoundary (canonicalWords K) (Sum.inl j) (canonicalWords_ne_nil K)) := by
  let f : OriginalRoseGen K → CanonicalGen K := Sum.inl
  have H := (ContinuousMap.Homotopic.refl (diskRoseMap f)).comp
    (boundaryWords_homotopic_classicalWord (originalRoseWords K j))
  rw [classicalRoseWordBoundary_map] at H
  have he : FreeGroup.mk (((originalRoseWords K j).loopWord).map (fun p => (f p.1, p.2))) =
      FreeGroup.mk (canonicalWords K (Sum.inl j)) := by
    calc
      _ = canonicalRelators K (Sum.inl j) := rfl
      _ = _ := (canonicalWords_mk K (Sum.inl j)).symm
  have Hword := classicalRoseWordBoundary_homotopic_of_mk_eq he
  have Hcanonical := classicalPresWordAttaching_homotopic_read
    (canonicalWords K) (Sum.inl j) (canonicalWords_ne_nil K)
  exact H.trans (Hword.trans Hcanonical.symm)

theorem stabilizedOriginalCellBoundary_dummy (u : PUnit) :
    (stabilizedOriginalCellBoundary K (Sum.inr u)).Homotopic
      (classicalPresCellBoundary (canonicalWords K) (Sum.inr u) (canonicalWords_ne_nil K)) := by
  cases u
  let f : PUnit → CanonicalGen K := Sum.inr
  have H := (ContinuousMap.Homotopic.refl (diskRoseMap f)).comp
    dummyCircleBoundaryHomeomorph_homotopic_word
  rw [classicalRoseWordBoundary_map] at H
  have he :=
    (canonicalWords_mk K (Sum.inr PUnit.unit)).symm
  have Hword := classicalRoseWordBoundary_homotopic_of_mk_eq he
  have Hcanonical := classicalPresWordAttaching_homotopic_read
    (canonicalWords K) (Sum.inr PUnit.unit) (canonicalWords_ne_nil K)
  exact H.trans (Hword.trans Hcanonical.symm)

theorem stabilizedOriginalCellBoundary_homotopic (j : CanonicalRel K) :
    (stabilizedOriginalCellBoundary K j).Homotopic
      (classicalPresCellBoundary (canonicalWords K) j (canonicalWords_ne_nil K)) := by
  grind [stabilizedOriginalCellBoundary_old, stabilizedOriginalCellBoundary_dummy]

/-- Disjoint-union topology assembles all the actual circle homotopies;
the original cell family is allowed to be infinite. -/
def originalCanonicalAttachingHomotopy :
    (StabilizedDiskPresentation.attaching (originalRoseWordAttaching K)).Homotopy
      (classicalPresWordAttaching (canonicalWords K) (canonicalWords_ne_nil K)) := by
  let H (j : CanonicalRel K) := Classical.choice (stabilizedOriginalCellBoundary_homotopic K j)
  exact FiniteChains.sigmaHomotopy H

/-- The original space itself, with no replacement hypothesis, is
homotopy equivalent to the literal canonical rose-and-word-disks model. -/
def originalClassicalPresWordDiskEquiv :
    ContinuousMap.HomotopyEquiv K
      (ClassicalPresWordDisks (presCanonicalWords (canonicalRelators K) (canonicalDummy K))
        (presCanonicalWords_ne_nil (canonicalRelators K) (canonicalDummy K))) :=
  ((originalWordDiskHomotopyEquiv K).trans
    (StabilizedDiskPresentation.homotopyEquiv (originalRoseWordAttaching K))).trans
      (diskAttachingHomotopyEquiv
        (StabilizedDiskPresentation.attaching (originalRoseWordAttaching K))
        (classicalPresWordAttaching (canonicalWords K) (canonicalWords_ne_nil K))
        (originalCanonicalAttachingHomotopy K))

def originalCanonicalRealizationEquiv :=
  (originalClassicalPresWordDiskEquiv K).trans
    (presClassicalDiskComparison (canonicalWords K) (canonicalWords_ne_nil K)).symm

variable (hK : Whitehead.FiniteCells K)
include hK

theorem canonicalGen_finite : Finite (CanonicalGen K) := by
  letI := originalRoseGen_finite K hK
  infer_instance

theorem canonicalRel_finite : Finite (CanonicalRel K) := by
  letI := originalRoseRel_finite K hK
  infer_instance

end FiniteChains.ClassicalCW
