import Mathlib.Tactic

import RequestProject.HomeomorphContinuousMap
import RequestProject.ClassicalCWWordDiskModel
import RequestProject.ClassicalRoseWordNaturality
import RequestProject.PresCircleWordParametrization
import RequestProject.PresCanonicalWords
import RequestProject.StabilizedDiskPresentation

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
def canonicalWords : CanonicalRel K → List (CanonicalGen K × Bool) :=
  presCanonicalWords (canonicalRelators K) (canonicalDummy K)

variable (j : CanonicalRel K)
abbrev canonicalWords_ne_nil   :=
  FiniteChains.PresModel.presCanonicalWords_ne_nil (FiniteChains.ClassicalCW.canonicalRelators K)
    (FiniteChains.ClassicalCW.canonicalDummy K) j

abbrev canonicalWords_mk   :=
  FiniteChains.PresModel.mk_presCanonicalWords (FiniteChains.ClassicalCW.canonicalRelators K)
    (FiniteChains.ClassicalCW.canonicalDummy K) j

def stabilizedOriginalCellBoundary   :=
  (StabilizedDiskPresentation.attaching (originalRoseWordAttaching K)).comp
    ⟨Sigma.mk (β := fun _ : CanonicalRel K => UnitBoundary (Fin 2 → ℝ)) j,
      continuous_sigmaMk⟩

abbrev stabilizedOriginalCellBoundary_old (j : OriginalRoseRel K)  :=
  let f := Sum.inl;
  have H :=
    ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl (FiniteChains.ClassicalGraphModel.diskRoseMap f))
      (FiniteChains.PresModel.boundaryWords_homotopic_classicalWord (FiniteChains.ClassicalCW.originalRoseWords K j));
  have he := Trans.trans rfl (Eq.symm (FiniteChains.ClassicalCW.canonicalWords_mk K (Sum.inl j)));
  have Hword := FiniteChains.PresModel.classicalRoseWordBoundary_homotopic_of_mk_eq he;
  have Hcanonical :=
    FiniteChains.PresModel.classicalPresWordAttaching_homotopic_read (FiniteChains.ClassicalCW.canonicalWords K)
      (Sum.inl j) (FiniteChains.ClassicalCW.canonicalWords_ne_nil K);
  ContinuousMap.Homotopic.trans
    (Eq.mp
      (congrArg
        (fun
            (_a :
              C(FiniteChains.RelativeAttachment.UnitBoundary (Fin 2 → ℝ),
                FiniteChains.ClassicalGraphModel.Rose (FiniteChains.ClassicalCW.CanonicalGen K))) =>
          ((FiniteChains.ClassicalGraphModel.diskRoseMap f).comp
                (FiniteChains.ClassicalCW.originalRoseWords K j).boundaryMap).Homotopic
            _a)
        (FiniteChains.PresModel.classicalRoseWordBoundary_map f
          (FiniteChains.ClassicalCW.originalRoseWords K j).loopWord))
      H)
    (ContinuousMap.Homotopic.trans Hword (ContinuousMap.Homotopic.symm Hcanonical))

theorem stabilizedOriginalCellBoundary_dummy (u : PUnit) :
    (stabilizedOriginalCellBoundary K (Sum.inr u)).Homotopic
      (classicalPresCellBoundary (canonicalWords K) (Sum.inr u) (canonicalWords_ne_nil K)) := by
  cases u
  let f : PUnit → CanonicalGen K := Sum.inr
  have H := (ContinuousMap.Homotopic.refl (diskRoseMap f)).comp
    dummyCircleBoundaryHomeomorph_homotopic_word
  rw [classicalRoseWordBoundary_map] at H
  have he : FreeGroup.mk ([(PUnit.unit, true)].map (fun p => (f p.1, p.2))) =
      FreeGroup.mk (canonicalWords K (Sum.inr PUnit.unit)) :=
    (canonicalWords_mk K (Sum.inr PUnit.unit)).symm
  have Hword := classicalRoseWordBoundary_homotopic_of_mk_eq he
  have Hcanonical := classicalPresWordAttaching_homotopic_read
    (canonicalWords K) (Sum.inr PUnit.unit) (canonicalWords_ne_nil K)
  exact H.trans (Hword.trans Hcanonical.symm)

theorem stabilizedOriginalCellBoundary_homotopic  :
    (stabilizedOriginalCellBoundary K j).Homotopic
      (classicalPresCellBoundary (canonicalWords K) j (canonicalWords_ne_nil K)) := by
  cases j with
  | inl j => exact stabilizedOriginalCellBoundary_old K j
  | inr u => exact stabilizedOriginalCellBoundary_dummy K u

/-- Disjoint-union topology assembles all the actual circle homotopies;
the original cell family is allowed to be infinite. -/
def originalCanonicalAttachingHomotopy :
    (StabilizedDiskPresentation.attaching (originalRoseWordAttaching K)).Homotopy
      (classicalPresWordAttaching (canonicalWords K) (canonicalWords_ne_nil K)) := by
  let H (j : CanonicalRel K) := Classical.choice (stabilizedOriginalCellBoundary_homotopic K j)
  let F : C(BoundaryFamily (CanonicalRel K) (Fin 2 → ℝ),
      C(I, ClassicalGraphModel.Rose (CanonicalGen K))) :=
    ⟨fun a => ((H a.1).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry a.2,
      continuous_sigma (fun j =>
        ((H j).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry.continuous)⟩
  exact {
    toContinuousMap := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := fun a => (H a.1).apply_zero a.2
    map_one_left := fun a => (H a.1).apply_one a.2 }

/-- The original space itself, with no replacement hypothesis, is
homotopy equivalent to the literal canonical rose-and-word-disks model. -/
def originalClassicalPresWordDiskEquiv  :=
  ((originalWordDiskHomotopyEquiv K).trans
    (StabilizedDiskPresentation.homotopyEquiv (originalRoseWordAttaching K))).trans
      (diskAttachingHomotopyEquiv
        (StabilizedDiskPresentation.attaching (originalRoseWordAttaching K))
        (classicalPresWordAttaching (canonicalWords K) (canonicalWords_ne_nil K))
        (originalCanonicalAttachingHomotopy K))

def originalCanonicalRealizationEquiv  :=
  (originalClassicalPresWordDiskEquiv K).trans
    (presClassicalDiskComparison (canonicalWords K) (canonicalWords_ne_nil K)).symm

theorem canonicalGen_finite (hK : Whitehead.FiniteCells K) : Finite (CanonicalGen K) := by
  letI := originalRoseGen_finite K hK
  infer_instance

theorem canonicalRel_finite (hK : Whitehead.FiniteCells K) : Finite (CanonicalRel K) := by
  letI := originalRoseRel_finite K hK
  infer_instance

end FiniteChains.ClassicalCW
