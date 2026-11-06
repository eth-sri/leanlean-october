import Mathlib.Tactic

import RequestProject.RelativeTreeAmbientChain
import RequestProject.TreeAcyclicExponentMatrix

/-! Unconditional relative chains over any acyclic combinatorial
two-complex with a spanning tree. All original cells and the full
fundamental-group data are retained. Pending final Lean verification. -/

noncomputable section

namespace FiniteChains.Comb
open SpanningTree RelativeNormalForm RelativeTreeAmbientChain

variable {D : Complex2.{0}} (T : SpanningTree D) (hD : IsAcyclic D)



def acyclicRelativeCellChain (n : ℕ)  :=
  actualRelativeChain T (expMatrix_bijective_of_acyclic T hD) n



end FiniteChains.Comb
