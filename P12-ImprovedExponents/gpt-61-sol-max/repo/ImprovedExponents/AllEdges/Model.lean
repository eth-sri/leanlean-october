module

public import ThreeSumApsp.Util.Types
public import Mathlib.Tactic
public import ImprovedExponents.AllEdges.Task
public import ImprovedExponents.HostMid.Claim

@[expose] public section

/-!
# The time model in which "Exact Triangle" is the all-edges version

Upstream's deductions between running-time claims are made for an arbitrary reading
`M : DetTimeModel` of "is solved in time `T`", and so are ours (`HostBound`, `Claim17Mid`,
`ExplicitFrom`, `explicitFrom_mid`).  `lightModelAE` is upstream's `lightModel` with one field
changed: `exactTriangle T` says that some procedure solves the all-edges version (`aeTask`) within
`T`.  The other fields are those of `lightModel`, definitionally; in particular a solver of
Lop-AE-SparseTri is the same thing in both models.

So a host that solves `aeTask` from a solver of Lop-AE-SparseTri within the bound of Theorem 17
(charged at the true size of the middle part) gives `Claim17Mid lightModelAE …`
(`claim17MidAE_of_host`), and the arithmetic of `ImprovedExponents.Total` then gives
`ExplicitFrom lightModelAE δ 1`: all-edges Exact Triangle in time `n^{3-δ} log n`.
-/

namespace ImprovedExponents.AllEdges

open Light

/-- Upstream's `lightModel`, with "Exact Triangle" read as all-edges Exact Triangle. -/
noncomputable def lightModelAE :=
  { lightModel with exactTriangle := SolvedIn aeTask }

end ImprovedExponents.AllEdges
