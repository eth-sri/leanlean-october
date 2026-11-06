import Mathlib.Tactic

import RequestProject.AcyclicRelativeTreeChains
import RequestProject.TreeChainFinsupp

/-! The actual regular-cover sufficiency construction in the cellular
category: build relative chains upstairs and descend their particular
maps. No finite-cell or spherical-generation premise remains. The
topological realization of this result is a separate bridge. Pending
final Lean verification. -/

noncomputable section

namespace FiniteChains.Comb
variable {D K : Complex2} (T : SpanningTree D) (hD : IsAcyclic D)
  (p : Hom D K)

def regularCoverChainStages (n : ℕ)  :=
  (acyclicRelativeCellChain T hD n).desc p

def regularCoverChainInclusion (n i : ℕ)  :=
  (acyclicRelativeCellChain T hD n).descInc p i



abbrev regularCoverChainInclusion_V (n i : ℕ)  :=
  FiniteChains.Comb.RelativeCellChain.descInc_injective_V (FiniteChains.Comb.acyclicRelativeCellChain T hD n) p i

abbrev regularCoverChainInclusion_E (n i : ℕ)  :=
  FiniteChains.Comb.RelativeCellChain.descInc_injective_E (FiniteChains.Comb.acyclicRelativeCellChain T hD n) p i

abbrev regularCoverChainInclusion_F (n i : ℕ)  :=
  FiniteChains.Comb.RelativeCellChain.descInc_injective_F (FiniteChains.Comb.acyclicRelativeCellChain T hD n) p i

abbrev regularCoverChain_connected (hp : IsCovering p) (n i : ℕ)  :=
  FiniteChains.Comb.RelativeCellChain.desc_connected (FiniteChains.Comb.acyclicRelativeCellChain T hD n) p hp T.root i

variable (hp : IsCovering p) {Q : Type v} [Group Q]
  (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (hf : ∀ q f, p.onF (a.smulF q f) = p.onF f)

include hp hr he hf in
abbrev regularCoverChain_zeroPi2 (n i : ℕ) (hi : i < n + 1)  :=
  FiniteChains.Comb.RelativeCellChain.descInc_zeroPi2 (FiniteChains.Comb.acyclicRelativeCellChain T hD n) p hp a hr he hf
    hD T.root i hi

/-- The actual descended inclusions form an arbitrary-length cellular
chain beginning literally at K. Strictness is regularCoverChain_proper. -/
def regularCoverTopChain (n : ℕ) : TopChainFS K (n + 1) where
  X := regularCoverChainStages T hD p n
  inc := regularCoverChainInclusion T hD p n
  incV := regularCoverChainInclusion_V T hD p n
  incE := regularCoverChainInclusion_E T hD p n
  incF := regularCoverChainInclusion_F T hD p n
  conn := regularCoverChain_connected T hD p hp n
  base := Hom.id K
  baseV := Function.injective_id
  baseE := Function.injective_id
  baseF := Function.injective_id
  zero_pi2 := regularCoverChain_zeroPi2 T hD p hp a hr he hf n

end FiniteChains.Comb
