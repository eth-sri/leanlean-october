import RequestProject.CombPushout


/-!
# Descending a chain along a covering: the combinatorial part of Proposition 3.11

Proposition 3.11 takes a chain `D = L₀ ⊆ L₁ ⊆ ⋯ ⊆ Lₙ` over an acyclic regular cover
`p : D → K` and descends it to a chain over `K` by forming the cellular pushouts
`Eᵢ = K ∪_p Lᵢ`.  Using the pushout of `RequestProject/CombPushout.lean` this file builds the
descended sequence and proves everything about it except the homotopy-theoretic statement
that its inclusions are zero on `π₂`:

* `FiniteChains.Comb.chainIncl` — the inclusion `L₀ ⊆ Lᵢ` obtained by composing the steps of
  the chain, and its injectivity;
* `FiniteChains.Comb.descentChain` — the descended sequence `E₀ = K`, `Eᵢ = K ∪_p Lᵢ`;
* `FiniteChains.Comb.descentChain_sub` — **every term is a subcomplex of the next**, so the
  descended sequence really is a chain of two-complexes starting at `K`;
* `FiniteChains.Comb.descentChain_finite_E`, `FiniteChains.Comb.descentChain_finite_F` — the
  stages are finite as soon as `K` is finite and each `Lᵢ` has only finitely many cells off
  `L₀`;
* `FiniteChains.Comb.descentChain_isConnected` — the stages are connected;
* `FiniteChains.Comb.exists_descentChain` — the packaged existence statement.

The chain upstairs is indexed by all of `ℕ`; a chain of finite length `n` is put in this form
by repeating its last term (`FiniteChains.Comb.sub_truncate`).
-/
