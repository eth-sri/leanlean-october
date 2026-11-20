module

public import RequestProject.ClassicalCWCanonicalPresentation
public import RequestProject.TopologicalCoverCellChains
public import RequestProject.TopologicalAcyclicCoverHomotopy
public import RequestProject.PresPosetConnected
public import RequestProject.PresPosetDimension

@[expose] public section

/-! Feed an acyclic regular covering of the original CW complex into
the actual cellular chain construction, through its constructed canonical
model. The remaining realization bridge must retain the original CW
cells when it turns these chains into Whitehead.HasChain. Pending final
Lean verification. -/

noncomputable section
open scoped Classical
namespace FiniteChains.ClassicalCW
open Comb PresModel CategoryTheory

abbrev CanonicalPos (K : Whitehead.TwoComplex) := PresPos (canonicalWords K)

instance canonicalPos_nonempty (K : Whitehead.TwoComplex) : Nonempty (CanonicalPos K) :=
  ⟨Sum.inl (Sum.inl Rose.base)⟩

instance canonicalPos_dimension (K : Whitehead.TwoComplex) :
    (nerve (CanonicalPos K)).HasDimensionLE 2 :=
  orderNerve_hasDimensionLE (presPosDimension (canonicalWords K))
    (presPosDimension_strictMono (canonicalWords K)) 2
    (presPosDimension_le_two (canonicalWords K))

def canonicalTwoComplex (K : Whitehead.TwoComplex) : Whitehead.TwoComplex :=
  orderNerveTwoComplex (CanonicalPos K) (presPos_isConnected _ (canonicalWords_ne_nil K))

def originalCanonicalTwoComplexEquiv (K : Whitehead.TwoComplex) :
    ContinuousMap.HomotopyEquiv K (canonicalTwoComplex K) :=
  originalCanonicalRealizationEquiv K

theorem canonicalTwoComplex_hasCover (K : Whitehead.TwoComplex)
    (h : Whitehead.HasAcyclicRegularCover K) :
    Whitehead.HasAcyclicRegularCover (canonicalTwoComplex K) :=
  Whitehead.hasAcyclicRegularCover_of_homotopyEquiv (canonicalTwoComplex K) K
    (originalCanonicalTwoComplexEquiv K).symm h

end FiniteChains.ClassicalCW
