module

public import RequestProject.InitialComplex
public import RequestProject.PresentationChain

@[expose] public section

/-!
# The initial pair as a chain of presentation complexes

`RequestProject/InitialComplex.lean` builds, over an acyclic complex `D` of a finite
presentation, the complex `Y_D` of Lemma 3.1 and proves the three assertions of that lemma:
`G(Y_D)` is free abelian on the added pairs of generators, `Y_D` is Cockcroft, and the
inclusion `D ⊂ Y_D` kills `π₁(D)` and is zero on `π₂`.

This file records the resulting pair as a genuine object of the framework of
`RequestProject/PresentationChain.lean`: `D ⊂ Y_D` is a chain
`FiniteChains.PresChain r 1` of nested presentation complexes whose single inclusion is
zero on `π₂`, i.e. the first step of condition (1) of Theorem A.  In particular the
hypothesis `zero_pi2` demanded there is exactly what Lemma 3.1 provides.
-/

namespace FiniteChains

universe u

variable {I J : Type u} [LinearOrder I] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The generators of the stages of the chain `D ⊂ Y_D`. -/
def genSeq (I : Type u) : ℕ → Type u
  | 0 => I
  | _ + 1 => GenY I

/-- The two-cells of the stages of the chain `D ⊂ Y_D`. -/
def cellSeq (I J : Type u) [LinearOrder I] : ℕ → Type u
  | 0 => J
  | _ + 1 => CellY I J

instance instDecGenSeq (k : ℕ) [DecidableEq I] : DecidableEq (genSeq I k) := by
  cases k <;> unfold genSeq <;> infer_instance

instance instFinGenSeq (k : ℕ) [Fintype I] [DecidableEq I] : Fintype (genSeq I k) := by
  cases k <;> unfold genSeq <;> infer_instance

instance instFinCellSeq (k : ℕ) [Fintype I] [DecidableEq I] [Fintype J] :
    Fintype (cellSeq I J k) := by
  cases k <;> unfold cellSeq <;> infer_instance

/-! ### The hypotheses are satisfiable -/

end FiniteChains
