module

public import QPBT.Games.CondLinear

/-!
# Reindexing of conditionally linear functions

A conditionally linear function of one register space transports along an
injective map of index types.  The transported function restricts a coefficient
vector to the registers named by that map, applies the original function, and
extends the result by zero outside the image; it is conditionally linear at the
same level on the full register.  In the one-level case the predicate holds of
every linear map of the ambient coefficient space, which is the converse
direction of the remark following `def:cl-func`.

## References

The source definition is `def:cl-func` in
`blueprint/src/chapter/ch12_qpbt_games.tex`, with paper origin
`references/qpbt-paper/05_conditionally_linear_functions.tex:35-57`.
-/

@[expose] public section

namespace MIPStarRE.QPBT





end MIPStarRE.QPBT
