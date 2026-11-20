module

public import RequestProject.StabilizedWordComparison
public import RequestProject.HomeomorphContinuousMap
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
def canonicalWords : CanonicalRel K → List (CanonicalGen K × Bool) :=
  presCanonicalWords (canonicalRelators K) (canonicalDummy K)

theorem canonicalWords_ne_nil (j : CanonicalRel K) : canonicalWords K j ≠ [] :=
  presCanonicalWords_ne_nil (canonicalRelators K) (canonicalDummy K) j

theorem canonicalWords_mk (j : CanonicalRel K) :
    FreeGroup.mk (canonicalWords K j) = canonicalRelators K j :=
  mk_presCanonicalWords (canonicalRelators K) (canonicalDummy K) j

/-- Disjoint-union topology assembles the relator homotopies. -/
def originalCanonicalAttachingHomotopy :
    (StabilizedDiskPresentation.attaching (originalRoseWordAttaching K)).Homotopy
      (classicalPresWordAttaching (canonicalWords K) (canonicalWords_ne_nil K)) :=
  stabilizedPresAttachingHomotopy _ (fun j => (originalRoseWords K j).loopWord) _ _
    (fun j => boundaryWords_homotopic_classicalWord (originalRoseWords K j))
    (fun j => (canonicalWords_mk K (Sum.inl j)).symm)
    (canonicalWords_mk K (Sum.inr PUnit.unit)).symm

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

def originalCanonicalRealizationEquiv :
    ContinuousMap.HomotopyEquiv K (Comb.orderNerveRealization (PresPos (canonicalWords K))) :=
  (originalClassicalPresWordDiskEquiv K).trans
    (presClassicalDiskComparison (canonicalWords K) (canonicalWords_ne_nil K)).symm

theorem canonicalGen_finite (hK : Whitehead.FiniteCells K) : Finite (CanonicalGen K) := by
  letI := originalRoseGen_finite K hK
  infer_instance

theorem canonicalRel_finite (hK : Whitehead.FiniteCells K) : Finite (CanonicalRel K) := by
  letI := originalRoseRel_finite K hK
  infer_instance

end FiniteChains.ClassicalCW
