module

public import Chazelle.Core.RestoreSearchArc

/-!
# WP-E, Lemma 3.2 part 16: descending the tree decomposition

The search descends the tree decomposition of a canonical normal form from its root, moving from
the node of a chord to one of its two children.  With a valid decomposition (`IsDecomp`, with the
properness clauses of finding R-D1):

* `Reach N x i`: the code `x` is reached from the root in `i` child steps;
* `reach_valid`, `reach_ne_root`, `reach_parent`: reached codes are valid, children are not the
  root, and `i` parent steps lead back to the root;
* `reach_le`: **at most `d` steps** (the depth of the decomposition);
* `reach_child`: the target region stays below the descent when the child on its side is taken;
* `leaf_eq`: at a leaf code, the region below is the leaf's own region.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

variable {N : NF} {d : ℕ}

section
variable (hD : IsDecomp N d) {k r : ℕ} (hk : k < N.nChords) (hb : N.Below (2 * k) r)
include hD hk hb
/-- **Taking the child on the side of the target keeps the target below.** -/
theorem below_lo
    (hs : r ∈ N.lowSide k) : N.Below (N.dnode k).lo r :=
  (hD.2.2.2.1 k hk r hb).2 hs

theorem below_hi
    (hs : r ∈ N.highSide k) : N.Below (N.dnode k).hi r :=
  (hD.2.2.2.2.1 k hk r hb).2 hs


end

/-- The target is below the root. -/
theorem below_root (hD : IsDecomp N d) {r : ℕ} (hr : r < N.nRegions) : N.Below N.root r :=
  hD.2.2.2.2.2.1 r hr

end

end Restore

end Chazelle.Core
