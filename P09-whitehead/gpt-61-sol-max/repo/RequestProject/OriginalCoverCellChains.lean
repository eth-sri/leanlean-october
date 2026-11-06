import Mathlib.Tactic

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

variable (K : Whitehead.TwoComplex)
abbrev CanonicalPos  := PresPos (canonicalWords K)

instance canonicalPos_nonempty (K : Whitehead.TwoComplex) : Nonempty (CanonicalPos K) :=
  ⟨Sum.inl (Sum.inl Rose.base)⟩

instance canonicalPos_dimension (K : Whitehead.TwoComplex) :
    (nerve (CanonicalPos K)).HasDimensionLE 2 :=
  orderNerve_hasDimensionLE (presPosDimension (canonicalWords K))
    (presPosDimension_strictMono (canonicalWords K)) 2
    (presPosDimension_le_two (canonicalWords K))

def canonicalTwoComplex   :=
  orderNerveTwoComplex (CanonicalPos K) (presPos_isConnected _ (canonicalWords_ne_nil K))

def originalCanonicalTwoComplexEquiv :=
  FiniteChains.ClassicalCW.originalCanonicalRealizationEquiv

abbrev canonicalTwoComplex_hasCover 
    (h : Whitehead.HasAcyclicRegularCover K)  :=
  Whitehead.hasAcyclicRegularCover_of_homotopyEquiv (FiniteChains.ClassicalCW.canonicalTwoComplex K) K
    (FiniteChains.ClassicalCW.originalCanonicalTwoComplexEquiv K).symm h

end FiniteChains.ClassicalCW
