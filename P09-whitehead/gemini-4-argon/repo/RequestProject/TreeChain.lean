module

public import RequestProject.TreeExtension
public import RequestProject.TreeCoverAcyclic
public import RequestProject.CoverComplex
public import RequestProject.PresentationDictionary
public import RequestProject.ChainFormula
public import RequestProject.FinitelyDeterminedInf
public import RequestProject.Pigeonhole
public import RequestProject.CoverAcyclic
public import RequestProject.NecessityAlgebraicMod
public import RequestProject.TorsionFreeGroupRing
public import RequestProject.ChainFormulaMod
public import RequestProject.PresUnivCoverIso
public import RequestProject.FoxNaturality
public import RequestProject.CycleLifting
public import RequestProject.Pi2Dictionary
public import RequestProject.CombData

@[expose] public section

/-!
# Condition (1) of Theorem A for chains of arbitrary two-complexes

`RequestProject/TreeCoverTheoremA.lean` proves `(1) ⇒ (2)` of Theorem A for a finite connected
two-complex `K`, but with condition (1) read over the *presentation complex* obtained by
collapsing a spanning tree of `K`.  The paper states condition (1) for chains
`K = X₀ ⊂ X₁ ⊂ ⋯ ⊂ Xₙ` of arbitrary two-complexes.  With the compatible collapse of
`RequestProject/TreeExtension.lean` the two readings can be joined:

* `FiniteChains.Comb.SpanningTree.exists_compatible_trees` — along any chain of subcomplex
  inclusions a spanning tree of the first stage extends to spanning trees of all stages, each
  meeting the previous stage exactly in the previous tree;
* `FiniteChains.Comb.SpanningTree.ComplexChain` — a chain of two-complexes over `K` together
  with such a compatible family of spanning trees, the inclusions being zero on `π₂` *after the
  collapse*;
* `FiniteChains.Comb.SpanningTree.ComplexChain.toPresChainTop` — collapsing the stages turns
  such a chain into a chain of presentation complexes, i.e. into a `FiniteChains.PresChainTop`;
* `FiniteChains.Comb.SpanningTree.hasAcyclicRegularCover_of_complexChains` — **`(1) ⇒ (2)` of
  Theorem A for chains of arbitrary finite two-complexes**: if chains of every length exist
  over `K`, then `K` has a connected acyclic regular cover.

Non-vacuity is checked at the end on the interval, whose collapse is the empty presentation.
-/

namespace FiniteChains.Comb.SpanningTree

universe u

/-! ### Compatible spanning trees along a chain -/

/-- **A spanning tree of the first stage of a chain extends to all stages**, each tree meeting
the previous stage exactly in the previous tree. -/
theorem exists_compatible_trees (X : ℕ → Complex2.{u}) (inc : ∀ r, Hom (X r) (X (r + 1)))
    (hconn : ∀ r, IsConnected (X r)) (hV : ∀ r, Function.Injective (inc r).onV)
    (hE : ∀ r, Function.Injective (inc r).onE) (T₀ : SpanningTree (X 0)) :
    ∃ T : ∀ r, SpanningTree (X r), T 0 = T₀ ∧
      ∀ (r : ℕ) (e : (X r).E), (T (r + 1)).isTree ((inc r).onE e) ↔ (T r).isTree e := by
  classical
  have step : ∀ (r : ℕ) (Tr : SpanningTree (X r)), ∃ T' : SpanningTree (X (r + 1)),
      ∀ e : (X r).E, T'.isTree ((inc r).onE e) ↔ Tr.isTree e := by
    intro r Tr
    obtain ⟨T', -, hT'⟩ :=
      exists_extension (inc r) (hconn (r + 1)) Tr.root Tr (hV r) (hE r)
    exact ⟨T', hT'⟩
  choose next hnext using step
  refine ⟨fun r => Nat.rec T₀ (fun r Tr => next r Tr) r, rfl, ?_⟩
  intro r e
  exact hnext r _ e
