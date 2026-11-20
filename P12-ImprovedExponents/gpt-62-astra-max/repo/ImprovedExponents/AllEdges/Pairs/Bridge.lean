module

public import ImprovedExponents.AllEdges.Task
public import ImprovedExponents.AllEdges.Pairs.Passes
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF
public import ThreeSumApsp.Util.Asymptotics.PowLittleO
public import ThreeSumApsp.Util.BinaryPrefixes

@[expose] public section

/-!
# The questions of the reduction from all pairs to all-edges Exact Triangle

Footnote 10 of the paper: the (min,+)-product reduces to the all-edges version of Exact Triangle
on the same `n` vertices.  The step from the threshold questions of upstream's `pairsTask`
("is there a `k` with `X[i,k] + Y[k,j] < V[i,j]`?") to zero triangles is Lemma F of the paper
(`ImprovedExponents.add_lt_iff_shiftDiff`, in the form `exists_lt_iff_exists_exactTriangle`): with
`b = aeLevels U` levels, `3U < 2^b ≤ 6U`, the threshold holds for some `k` if and only if one of
the `2b + 3` instances `(ℓ, r) ∈ lemmaFInstances b` has a zero triangle through `(i, j)`.

The instance `(ℓ, r)` has, in the convention of `aeTask` (`AB` at `a n + b`, `BC` at `b n + c`,
`AC` at `a n + c`, with `a = i`, `b = j`, `c = k`), the matrices `r − ⌊(V + 2U)/2^ℓ⌋` (`instAB`),
the transpose of `⌊(Y + U)/2^ℓ⌋` (`instBC`) and `⌊(X + U)/2^ℓ⌋` (`instAC`).  `pairFlags_iff`
is the bridge, `absLe_inst*` bound the weights by `9U`, and `orFlags` with `orL_orFlags` describes
the disjunction of the flags of the instances asked so far.
-/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-- The number of levels: for `U ≥ 1`, the least `b` with `2^b > 3U`. -/
def aeLevels (U : ℕ) : ℕ := Nat.log 2 (3 * U) + 1

theorem lt_two_pow_aeLevels (U : ℕ) : 3 * U < 2 ^ aeLevels U :=
  Nat.lt_pow_succ_log_self (by norm_num) _

theorem two_pow_aeLevels_le {U } (hU : 1 ≤ U) : 2 ^ aeLevels U ≤ 6 * U := by
  have := Nat.pow_log_le_self 2 (show 3 * U ≠ 0 by omega)
  rw [aeLevels]
  omega

/-! ## The lists of the instances -/

section Lists

variable {n U : ℕ} {X Y V : List ℤ}

/-- The entries of the prefixes of a list of numbers in `[0, B]` lie in `[0, B]`. -/
theorem absLe_map_prefQ {l : List ℤ} {B } (h : ∀ z ∈ l, 0 ≤ z ∧ z ≤ B) (ℓ : ℕ) :
    ∀ z ∈ l.map (prefQ ℓ), 0 ≤ z ∧ z ≤ B := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
  exact ⟨prefQ_nonneg (h y hy).1 ℓ, (prefQ_le (h y hy).1 ℓ).trans (h y hy).2⟩

/-! ## The bridge -/

end Lists

/-! ## The disjunction of the flags of the instances asked so far -/

end ImprovedExponents.AllEdges
