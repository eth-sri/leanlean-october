/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import GalvinLib.Galvin

/-!
# Proofs of the statements in `Challenge.lean`

The theorems are proved in `GalvinLib/` (namespace `Galvin`). `GaleShapley.lean` proves the
existence of stable matchings by strong induction on the number of acceptable pairs (if two
men share a favourite woman, delete the pair she likes less). `Kernel.lean` proves the kernel
lemma: if every set of vertices of a digraph has a kernel and every list is longer than the
out-degree, there is a proper list colouring. `Orientation.lean` orients the line graph of a
bipartite graph using a proper `Δ`-edge-colouring from Kőnig's theorem (`Konig/Basic.lean`, from
the registered entry PALOMAR-2026-10-15-000019, included unchanged): every out-degree is below
`Δ`, and every set of edges has a kernel, given by a stable matching. The Dinitz problem is the
case of `K_{n,n}`.
-/

@[expose] public section

namespace ListEdgeColouring

/-- **Gale–Shapley (1962).** For a bipartite acceptability relation `E` between finite sets `M`
and `W`, with strict preferences given by injective rank functions (`rm m w < rm m w'` means that
`m` prefers `w` to `w'`), there is a stable matching. -/
alias gale_shapley := Galvin.gale_shapley

/-- **Galvin's theorem (1995).** If every edge of a finite bipartite graph `G` has a list of at
least `Δ(G)` colours, then `G` has a proper edge colouring choosing every colour from the list of
its edge. -/
alias galvin := Galvin.galvin

/-- **The Dinitz problem** (Galvin 1995). If every cell of an `n × n` array has a list of at least
`n` symbols, there is a choice of one symbol from each list with all symbols in each row distinct
and all symbols in each column distinct. -/
alias dinitz := Galvin.dinitz

end ListEdgeColouring
