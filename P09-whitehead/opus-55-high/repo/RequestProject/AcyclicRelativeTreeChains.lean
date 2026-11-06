import RequestProject.RelativeTreeAmbientChain
import RequestProject.TreeAcyclicExponentMatrix


/-! Unconditional relative chains over any acyclic combinatorial
two-complex with a spanning tree. All original cells and the full
fundamental-group data are retained. Pending final Lean verification. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb
open SpanningTree RelativeNormalForm RelativeTreeAmbientChain

variable {D : Complex2.{0}} (T : SpanningTree D) (hD : IsAcyclic D)

def acyclicRelativeStages (n : ℕ) : ℕ → Complex2 :=
  stages T (actualAmbientChain _ (expMatrix_bijective_of_acyclic T hD) n)

def acyclicRelativeCellChain n :
    RelativeCellChain (acyclicRelativeStages T hD n) (n + 1) :=
  actualRelativeChain T _ n
