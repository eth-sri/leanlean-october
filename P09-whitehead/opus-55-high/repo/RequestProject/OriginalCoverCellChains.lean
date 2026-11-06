import RequestProject.ClassicalCWCanonicalPresentation
import RequestProject.TopologicalCoverCellChains
import RequestProject.TopologicalAcyclicCoverHomotopy
import RequestProject.PresPosetConnected
import RequestProject.PresPosetDimension


/-! Feed an acyclic regular covering of the original CW complex into
the actual cellular chain construction, through its constructed canonical
model. The remaining realization bridge must retain the original CW
cells when it turns these chains into Whitehead.HasChain. Pending final
Lean verification. -/

noncomputable section
namespace FiniteChains.ClassicalCW
open Comb PresModel CategoryTheory

abbrev CanonicalPos (K : Whitehead.TwoComplex) := PresPos (canonicalWords K)

instance canonicalPos_nonempty K : Nonempty (CanonicalPos K) :=
  by tauto

instance canonicalPos_dimension K :
    (nerve (CanonicalPos K)).HasDimensionLE 2 :=
  orderNerve_hasDimensionLE _
    (presPosDimension_strictMono _) 2
    (presPosDimension_le_two _)

def canonicalTwoComplex (K : Whitehead.TwoComplex) :=
  orderNerveTwoComplex (CanonicalPos K) (presPos_isConnected _ (canonicalWords_ne_nil K))

def originalCanonicalTwoComplexEquiv (K : Whitehead.TwoComplex) :
    ContinuousMap.HomotopyEquiv K (canonicalTwoComplex K) :=
  originalCanonicalRealizationEquiv K

theorem canonicalTwoComplex_hasCover K
    (h : Whitehead.HasAcyclicRegularCover K) :
    Whitehead.HasAcyclicRegularCover (canonicalTwoComplex K) :=
  Whitehead.hasAcyclicRegularCover_of_homotopyEquiv _ K
    (originalCanonicalTwoComplexEquiv K).symm h
