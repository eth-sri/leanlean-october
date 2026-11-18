module

public import RequestProject.TreeExtension
public import RequestProject.TreeCoverExample
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

namespace FiniteChains
namespace Comb
namespace SpanningTree

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

/-! ### Chains of two-complexes -/

/-- A chain `K ⊂ X₀ ⊂ X₁ ⊂ ⋯ ⊂ Xₙ` of two-complexes over `K`, equipped with spanning trees
extending the given spanning tree `T₀` of `K`, whose inclusions are zero on `π₂` after the
collapse of those trees.  This is condition (1) of Theorem A for a general two-complex: by
`FiniteChains.Comb.SpanningTree.exists_compatible_trees` the trees are never an obstruction,
the content of the data being the chain itself and the vanishing on `π₂`. -/
structure ComplexChain (K : Complex2.{u}) (T₀ : SpanningTree K) (n : ℕ) where
  /-- The stages of the chain. -/
  X : ℕ → Complex2.{u}
  /-- The spanning tree of the stage `X r`. -/
  T : ∀ r, SpanningTree (X r)
  /-- The inclusion of `X r` in `X (r + 1)`. -/
  inc : ∀ r, Hom (X r) (X (r + 1))
  incE : ∀ r, Function.Injective (inc r).onE
  incF : ∀ r, Function.Injective (inc r).onF
  /-- The tree of `X (r + 1)` meets `X r` exactly in the tree of `X r`. -/
  tree_inc : ∀ (r : ℕ) (e : (X r).E), (T (r + 1)).isTree ((inc r).onE e) ↔ (T r).isTree e
  /-- The inclusion of `K` in the first stage. -/
  base : Hom K (X 0)
  baseE : Function.Injective base.onE
  baseF : Function.Injective base.onF
  /-- The tree of the first stage meets `K` exactly in `T₀`. -/
  tree_base : ∀ e : K.E, (T 0).isTree (base.onE e) ↔ T₀.isTree e
  decGen : ∀ r, DecidableEq (NonTree (T r))
  finGen : ∀ r, Fintype (NonTree (T r))
  finCell : ∀ r, Fintype (X r).F
  /-- **The inclusion `X r ⊂ X (r + 1)` is zero on `π₂`**, read on the collapsed presentation
  complexes. -/
  zero_pi2 : ∀ r, r < n →
      letI := decGen r
      letI := decGen (r + 1)
      Comb.ZeroPi2 (presInclHom (nonTreeIncl (tree_inc r))
        (nonTreeIncl_injective (tree_inc r) (incE r)) (treeRel (T r)) (treeRel (T (r + 1)))
        (inc r).onF (treeRel_onF (tree_inc r)))

namespace ComplexChain

variable {K : Complex2.{u}} {T₀ : SpanningTree K} {n : ℕ} (c : ComplexChain K T₀ n)

end ComplexChain

variable {K : Complex2.{u}} (T₀ : SpanningTree K)
variable [Fintype (NonTree T₀)] [DecidableEq (NonTree T₀)] [Fintype K.F] [DecidableEq K.F]

/-! ### Non-vacuity -/

end SpanningTree
end Comb
end FiniteChains
