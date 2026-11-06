module

public import RequestProject.RelativeTreeAmbientChain
public import RequestProject.TreeAcyclicExponentMatrix

@[expose] public section

/-! Unconditional relative chains over any acyclic combinatorial
two-complex with a spanning tree. All original cells and the full
fundamental-group data are retained. Pending final Lean verification. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb
open SpanningTree RelativeNormalForm RelativeTreeAmbientChain

variable {D : Complex2.{0}} (T : SpanningTree D) (hD : IsAcyclic D)

def acyclicRelativeStages (n : ℕ) : ℕ → Complex2 :=
  stages T (actualAmbientChain (treeRel T) (expMatrix_bijective_of_acyclic T hD) n)

def acyclicRelativeCellChain (n : ℕ) :
    RelativeCellChain (acyclicRelativeStages T hD n) (n + 1) :=
  actualRelativeChain T (expMatrix_bijective_of_acyclic T hD) n

@[simp] theorem acyclicRelativeStages_zero (n : ℕ) :
    acyclicRelativeStages T hD n 0 = D := rfl

end FiniteChains.Comb
