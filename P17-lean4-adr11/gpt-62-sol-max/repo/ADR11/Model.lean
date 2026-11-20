module

public import ADR11.SmallTrees
public import ADR11.MSC.Basic
public import ADR11.Model.History
public import ADR11.Computation.Caterpillar5

/-!
# Section 3: the multispecies coalescent model

* `rootedDist_nonneg`, `rootedDist_sum`, `unrootedDist_nonneg`, `unrootedDist_sum`: the model
  defines probability distributions on rooted and on unrooted gene trees (Section 1).
* `equation2`: Tavaré's formula [Tavaré 1984] for `g_ij(t)`, the probability that `i` lineages
  coalesce into `j` lineages within time `t` (`ADR11.coalescenceProb`).
* `coalescenceProb_nonneg`, `coalescenceProb_sum`: for `i > 1` and `t > 0`, the `g_ij(t)`,
  `j = 1, …, i`, form a probability distribution; `tendsto_coalescenceProb_one`:
  `g_i1(t) → 1` as `t → ∞`; `tendsto_coalescenceProb_self`: `g_ii(t) → 1` as `t → 0`;
  `coalescenceProb_self`: `g_ii(t) = exp(-i(i-1)t/2)`.
* `section3_example1`, `section3_example2`: the two worked examples of rooted gene tree
  probabilities in the caterpillar species tree `((((a,b):x,c):y,d):z,e)`.
* `equation3`: gene tree probabilities are sums, over finitely many coalescent histories, of a
  constant depending only on the topologies times a product of `g`'s, as in equation (3).
* `section3_polynomial`: rooted and unrooted gene tree probabilities are polynomials, with
  rational coefficients, in the transformed branch lengths `exp(-x_b)`.
* `rootedDist_eq_of_sameRootedMetricTree`: with one lineage per taxon, pendant edge lengths do
  not matter (Section 2).
* `rootedDist_support`: gene trees are binary with probability `1` (Sections 1 and 5).
-/

@[expose] public section

namespace ADR11

open Finset Real Filter Topology

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Section 1: the unrooted gene tree probabilities form a well-defined probability distribution:
they are nonnegative ... -/
theorem unrootedDist_nonneg {L : Type*} [Fintype L] [DecidableEq L] (σ : SpeciesTree X)
    (s : L → X) (T : Finset (Finset L)) : 0 ≤ σ.unrootedDist s T :=
  unrootedDistOf_nonneg σ.isHierarchy (fun A hA hAu => (σ.length_pos A hA hAu).le) s T

/-- ... and sum to `1`. -/
theorem unrootedDist_sum {L : Type*} [Fintype L] [DecidableEq L] (σ : SpeciesTree X)
    (s : L → X) : ∑ T, σ.unrootedDist s T = 1 :=
  unrootedDistOf_sum σ.isHierarchy σ.length s

end ADR11
