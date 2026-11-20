module

public import QPBT.Games.CondLinear

/-!
# Coordinate direct sums of conditionally linear representations

Equal-level representations of conditionally linear functions over pairwise
disjoint registers have a coordinatewise direct sum. Restriction to one
register selects its supported summand, and a supported representation is
unchanged when its input is restricted to that register. These identities give
the support and evaluation properties used by the shared-seed product law.

## References

The source result is blueprint `lem:cl-func-prod`, approached through the
formalization support nodes `lem:cl-supported-vanishing`,
`lem:cl-restriction-idem`, `lem:cl-restriction-sum`,
`lem:cl-supported-restriction`, and `lem:cl-func-prod-same-level` in
`ch12_qpbt_games.tex`.  The paper origin is
`references/qpbt-paper/05_conditionally_linear_functions.tex:150-379`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- Restricting first to a larger register does not affect a subsequent
restriction to a smaller register.  This is a formalization-only auxiliary
for `lem:cl-kth` and `lem:cl-func-prod`, blueprint
`lem:cl-restriction-idem`. -/
theorem coordinateRestriction_coordinateRestriction {K ι : Type*} [Field K]
    [DecidableEq ι] {S T : Finset ι} (hST : S ⊆ T) (x : ι → K) :
    coordinateRestriction S (coordinateRestriction T x) = coordinateRestriction S x := by
  ext a
  by_cases ha : a ∈ S
  · simp [coordinateRestriction, ha, hST ha]
  · simp [coordinateRestriction, ha]

end MIPStarRE.QPBT
