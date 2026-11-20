module

public import ADR11.MSC.Pullback
public import ADR11.MSC.Marginal

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Equal unrooted gene tree distributions give equal distributions on every induced subtree
(Lemma 5). -/
theorem unrootedDist_restrict_eq {σ σ' : SpeciesTree X}
    (h : σ.unrootedDist id = σ'.unrootedDist id) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).unrootedDist id = (σ'.restrict S hS).unrootedDist id := by
  simp only [SpeciesTree.restrict,SpeciesTree.unrootedDist_pull]; exact sample_eq h (Function.Embedding.subtype (· ∈ S))

end ADR11
