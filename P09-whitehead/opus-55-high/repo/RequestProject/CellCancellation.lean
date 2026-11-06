import Mathlib


/-!
# Cancelling the polygon-cylinder three-cell against the replaced two-cell

The substitution (3.4) of the paper is obtained from the double mapping cylinder by two
simplifications:

> In the double mapping cylinder, the polygon-cylinder three-cell cancels that old two-cell.
> Eliminating the edge-cylinder defining pairs then gives exactly (3.4).

This file proves the algebraic content of the first simplification at the level of the
equivariant cellular chain complexes.  The three-chains are free of rank one over the group
ring on the polygon-cylinder cell, and the coefficient of the replaced two-cell in its
boundary is a unit (the cell is crossed exactly once): in the notation below the two-chains
split as `P × Q` — `P` the retained two-cells, `Q` the free module on the replaced one — and
the boundary `∂₃ = (α, β)` has `β` invertible.

* `FiniteChains.Cancel.cancelMap` — the chain-level cancellation `κ(p, q) = (p - α β⁻¹ q, 0)`;
* `FiniteChains.Cancel.cancelMap_boundary` — it kills the three-boundaries;
* `FiniteChains.Cancel.cycle_sub_boundary_eq` — every two-cycle becomes, after cancellation,
  a two-cycle supported on the retained two-cells, and it differs from the original one by a
  three-boundary;
* `FiniteChains.Cancel.mem_range_boundary_iff` — a chain supported on the retained two-cells
  is a three-boundary only if it is zero, so the cancelled complex computes `H₂` on the nose;
* `FiniteChains.Cancel.generation_after_cancellation` — **the transfer of the generation
  statement**: if the two-cycles of the three-dimensional complex are spanned, modulo
  three-boundaries, by a set `S`, then the two-cycles of the cancelled two-dimensional
  complex are spanned by the cancelled images of `S`.  This is the step which turns the
  homological statement about the double mapping cylinder into the statement about the
  two-complex of the substituted presentation.
-/
