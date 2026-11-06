module

public import Chazelle.Separator.Cotree

/-!
# Deleting and contracting an edge (planar separators, part 2b)

**Deletion** (`CombMap.deleteEdge`).  Let `n` be a dart whose two sides are distinct faces
(`face n ≠ face (opp n)`), excluding the lone loop (`rot n = opp n` and `rot (opp n) = n`, whose
vertex would disappear).  The new map has the darts `D₀ = {x // x ≠ n ∧ x ≠ opp n}`, the
rotation is the first-return map of `rot` to `D₀`, the vertices are unchanged, and the two faces
of `n` merge: faces `{g // g ≠ face (opp n)}`.  So `V' = V`, `E' = E - 1`, `F' = F - 1`;
connectivity and hence planarity are preserved (`deleteEdge_planar`).  The face permutation of
the new map is the first-return map of `fperm * swap n (opp n)` (`deleteEdge_fperm_eq`), whose
cycles are the old faces with the two faces of `n` merged (`sameCycle_mul_swap_iff`).

**Contraction** (`CombMap.contractEdge`) of a non-loop edge is deletion in the dual map:
`M / e = (M.dual − e).dual`; it merges the two endpoints (`V' = V - 1`, `E' = E - 1`, `F' = F`)
and preserves planarity (`contractEdge_planar`).

These operations are not used by the separator proof (which only adds edges); they complete the
toolkit of `Operations.lean`.
-/

namespace Chazelle.Separator

@[expose] public section

open Equiv Finset

namespace CombMap

variable {V F D : Type*} [Fintype D] [DecidableEq D] [DecidableEq F] (M : CombMap V F D)



/-! ### Contraction as deletion in the dual -/



end CombMap

end

end Chazelle.Separator
