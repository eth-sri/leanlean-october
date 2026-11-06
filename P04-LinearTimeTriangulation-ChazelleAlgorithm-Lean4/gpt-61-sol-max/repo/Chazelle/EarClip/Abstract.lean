module

public meta import Chazelle.Arithmetic

public import Chazelle.EarClip.SubPoly

/-!
# The abstract ear-clipping algorithm

The remaining polygon is a list `l` of original indices (`subPoly P l`, see `SubPoly.lean`).

* `earTest P l p`: the arithmetic ear test at position `p` of `l`, literally the right-hand
  side of `Chazelle.Ears.isEar_iff` for `Q = subPoly P l`; so `earTest P l p ↔ IsEar Q p`
  whenever `Q` is simple, `4 ≤ l.length` and `p < l.length` (`earTest_iff_isEar`).
  `earTest_iff_list` restates it on original indices (for `l.Nodup`), and `earTest_rotate`
  shows that testing position `1` of `l.rotate r` is testing position `(r + 1) % m` of `l`.
* **Scan order.**  `findEar P l` returns the first position, in the order
  `1, 2, …, m - 1, 0` (i.e. position `(r + 1) % m` for `r = 0, 1, …, m - 1`: this is the RAM
  loop, which tests the corner `j = next i` and rotates `i := j` on failure), that passes the
  test (`findEar_some`, `findEar_none`, `findEar_some_of_exists`).
* `earTri l p := (l.getD ((p + m - 1) % m) 0, l.getD p 0, l.getD ((p + 1) % m) 0)` is the emitted
  triangle `(l[p-1], l[p], l[p+1])` in original indices.
* `earClipStep P l = (findEar P l).map fun p => (earTri l p, clipList l p)` is one step:
  the emitted triangle and the new list, which starts at the predecessor `l[p-1]`.
* `earClipList P l`: while `3 < l.length`, step; finally emit `(l[0], l[1], l[2])`.
  `earClip P := earClipList P (List.range P.n)`.
* `Inv P l := l.Nodup ∧ (∀ x ∈ l, x < P.n) ∧ 3 ≤ l.length ∧ (subPoly P l).Simple` is preserved
  by a step (`inv_step`), and a step exists whenever `3 < l.length` (`earClipStep_isSome`).
* **Correctness**: `earClip_weakTriangulates`, `earClip_triangulates`, `length_earClip`.
-/

namespace Chazelle.EarClip

@[expose] public section

open Chazelle.Jordan
open Chazelle.Existence
open Chazelle.Ears
open Chazelle.Geometry (lerp)

variable (P : Polygon)

/-! ### The ear test -/

section
variable (l : List ℕ)
/-- The predecessor index of position `p` in a list of length `m`. -/
theorem prevIdx_subPoly (p : ℕ) :
    prevIdx (subPoly P l) p = (p + l.length - 1) % l.length := by
  core_grind [n_subPoly]

/-- `getD` of a rotated list. -/
theorem getD_rotate (r k : ℕ) (hk : k < l.length) (d : ℕ) :
    (l.rotate r).getD k d = l.getD ((k + r) % l.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_rotate hk]

/-! ### Finding an ear: scan order `1, 2, …, m - 1, 0` -/

/-! ### The algorithm -/


end

section
variable (l : List ℕ) (p : ℕ)
include l p
/-- The emitted triangle at position `p`: `(l[p-1], l[p], l[p+1])` in original indices. -/
def earTri : Polygon.Triangle :=
  (l.getD ((p + l.length - 1) % l.length) 0, l.getD p 0, l.getD ((p + 1) % l.length) 0)

/-- `earTri` is the ear triangle of `subPoly P l` relabelled to original indices. -/
theorem relabelList_earTriangle :
    relabelList l (earTriangle (subPoly P l) p) = earTri l p := by
  unfold relabelList earTriangle earTri
  rw [prevIdx_subPoly, n_subPoly]

/-! ### The invariant -/

/-! ### Correctness -/


end

end

end Chazelle.EarClip
