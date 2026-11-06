module

public import Chazelle.Ears.Basic
public import Chazelle.Ears.Test
public import Chazelle.Ears.Exists
public import Mathlib.Data.List.Rotate

/-!
# Sub-polygons on a list of original indices

The ear-clipping algorithm maintains the *remaining polygon* as a list `l : List ℕ` of
original vertex indices of `P`, in boundary order.  The remaining polygon is
`subPoly P l := ⟨l.map P.vtx⟩`: its vertex `j` is `P.vtx l[j]` and its `n` is `l.length`.

## Conventions fixed here (shared with the RAM implementation)

* `subPoly P (List.range P.n) = P` (`subPoly_range`).
* `subPoly P (l.rotate r) = (subPoly P l).rotate r` (`subPoly_rotate`).
* **Clipping.**  For `l` of length `m` and a position `p < m`,
  `clipList l p := (l.rotate (p + m - 1)).eraseIdx 1`
  is the list with `l[p]` removed, *starting at the predecessor* `l[(p + m - 1) % m]`:
  `(clipList l p)[0] = l[(p + m - 1) % m]` and `(clipList l p)[k] = l[(p + k) % m]` for
  `1 ≤ k < m - 1` (`getElem?_clipList`, `getD_clipList`).  For `1 ≤ p` this is
  `(l.rotate (p - 1)).eraseIdx 1` (`clipList_eq_rotate_eraseIdx`), and `clipList l 1 = l.eraseIdx 1`.
  Geometrically, `subPoly P ((clipList l p).rotate 1) = Chazelle.Ears.clip (subPoly P l) p`
  (`subPoly_clipList_rotate`), equivalently
  `subPoly P (clipList l p) = (clip (subPoly P l) p).rotate (m - 2)` (`subPoly_clipList_eq`).
* **Triangles.**  A triangle of `subPoly P l` is given by positions in `l`;
  `relabelList l t := (l.getD t.1 0, l.getD t.2.1 0, l.getD t.2.2 0)` maps it to original indices
  (`triSet_relabelList`, `triVertices_relabelList`, `validTriangle_relabelList`).
* `weakTriangulates_rotate`: the weak version of `Chazelle.Existence.triangulates_rotate`.
* `weakTriangulates_clipList`: the ear-clipping step for sub-polygons: a weak triangulation `T`
  of `subPoly P (clipList l p)` (in positions of `clipList l p`) yields the weak triangulation
  `earTriangle (subPoly P l) p :: T.map (clipRelabel m p)` of `subPoly P l` (in positions of `l`),
  where `clipRelabel m p` is the position map `clipList l p → l`; on original indices
  `relabelList l (clipRelabel m p t) = relabelList (clipList l p) t` (`relabelList_clipRelabel`).
-/

namespace Chazelle.EarClip

@[expose] public section

open Chazelle.Jordan
open Chazelle.Existence
open Chazelle.Ears

/-! ### Elementary list facts -/

/-- `getD` at an in-range index is `getElem`. -/
theorem getD_eq_getElem_of_lt {α : Type} (l : List α) (d : α) {i : ℕ} (hi : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- `(range n).getD i 0 = i` for `i < n`. -/
theorem getD_range {n i : ℕ} (hi : i < n) : (List.range n).getD i 0 = i := by
  rw [getD_eq_getElem_of_lt _ _ (by simpa using hi), List.getElem_range]

/-- Two polygons with the same vertex list are equal. -/
theorem polygon_ext {P Q : Polygon} (h : P.vertices = Q.vertices) : P = Q := by
  cases P; cases Q; simp_all

/-! ### The sub-polygon -/

/-- The sub-polygon of `P` on the index list `l`: vertex `j` is `P.vtx l[j]`. -/
def subPoly (P : Polygon) (l : List ℕ) : Polygon := ⟨l.map P.vtx⟩

variable (P : Polygon)

/-- The vertex list of `subPoly P l`. -/
theorem vertices_subPoly (l : List ℕ) : (subPoly P l).vertices = l.map P.vtx := rfl

/-- `subPoly P l` has `l.length` vertices. -/
@[simp] theorem n_subPoly (l : List ℕ) : (subPoly P l).n = l.length := by
  simp [subPoly, Polygon.n]

/-- Vertex `j < l.length` of `subPoly P l` is `P.vtx l[j]`. -/
theorem vtx_subPoly (l : List ℕ) {j : ℕ} (hj : j < l.length) :
    (subPoly P l).vtx j = P.vtx l[j] := by
  simp [subPoly, Polygon.vtx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

/-- Vertex `j < l.length` of `subPoly P l` is `P.vtx (l.getD j 0)`. -/
theorem vtx_subPoly_getD (l : List ℕ) {j : ℕ} (hj : j < l.length) :
    (subPoly P l).vtx j = P.vtx (l.getD j 0) := by
  rw [vtx_subPoly P l hj, getD_eq_getElem_of_lt l 0 hj]

/-- `subPoly P (List.range P.n) = P`. -/
theorem subPoly_range : subPoly P (List.range P.n) = P := by
  apply polygon_ext
  rw [vertices_subPoly]
  apply List.ext_getElem
  · simp [Polygon.n]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact getD_eq_getElem_of_lt _ _ h2

/-- Rotating the index list rotates the sub-polygon. -/
theorem subPoly_rotate (l : List ℕ) (r : ℕ) :
    subPoly P (l.rotate r) = (subPoly P l).rotate r := by
  apply polygon_ext
  rw [vertices_subPoly]
  unfold Polygon.rotate
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < l.length := by simpa using h1
    simp only [List.getElem_map, List.getElem_rotate, List.getElem_range, n_subPoly]
    rw [vtx_subPoly P l (Nat.mod_lt _ (by omega)), Nat.add_comm r i]

/-! ### Clipping a position -/

/-- The list with position `p` removed, starting at the predecessor `l[(p + m - 1) % m]`. -/
def clipList (l : List ℕ) (p : ℕ) : List ℕ := (l.rotate (p + l.length - 1)).eraseIdx 1

/-- `clipList` for `1 ≤ p`: rotate by `p - 1` and erase position `1`. -/
theorem clipList_eq_rotate_eraseIdx (l : List ℕ) {p : ℕ} (hp : 1 ≤ p) :
    clipList l p = (l.rotate (p - 1)).eraseIdx 1 := by
  unfold clipList
  rw [show p + l.length - 1 = (p - 1) + l.length by omega, ← List.rotate_mod,
    Nat.add_mod_right, List.rotate_mod]

/-- The clipped list has one element fewer. -/
theorem length_clipList (l : List ℕ) (p : ℕ) (h2 : 2 ≤ l.length) :
    (clipList l p).length = l.length - 1 := by
  unfold clipList
  rw [List.length_eraseIdx_of_lt (by rw [List.length_rotate]; omega), List.length_rotate]

/-- The entries of the clipped list: position `0` is the predecessor `l[(p + m - 1) % m]`,
position `k ≥ 1` is `l[(p + k) % m]`. -/
theorem getElem?_clipList (l : List ℕ) (p : ℕ) (h2 : 2 ≤ l.length) {k : ℕ}
    (hk : k < l.length - 1) :
    (clipList l p)[k]? =
      if k = 0 then l[(p + l.length - 1) % l.length]? else l[(p + k) % l.length]? := by
  unfold clipList
  rw [List.getElem?_eraseIdx]
  split_ifs with h1 h0 h0
  · rw [List.getElem?_rotate (by omega)]
    subst h0
    rw [Nat.zero_add]
  · omega
  · omega
  · rw [List.getElem?_rotate (by omega)]
    congr 1
    rw [show k + 1 + (p + l.length - 1) = p + k + l.length by omega, Nat.add_mod_right]

/-- `getD` version of `getElem?_clipList`. -/
theorem getD_clipList (l : List ℕ) (p : ℕ) (h2 : 2 ≤ l.length) {k : ℕ}
    (hk : k < l.length - 1) (d : ℕ) :
    (clipList l p).getD k d =
      if k = 0 then l.getD ((p + l.length - 1) % l.length) d else l.getD ((p + k) % l.length) d := by
  rw [List.getD_eq_getElem?_getD, getElem?_clipList l p h2 hk]
  split_ifs <;> rw [List.getD_eq_getElem?_getD]

/-- The clipped list, rotated by one (so that it starts at the successor `l[(p + 1) % m]`),
is the vertex list of `Chazelle.Ears.clip (subPoly P l) p`. -/
theorem subPoly_clipList_rotate (l : List ℕ) (p : ℕ) (h3 : 3 ≤ l.length) (hp : p < l.length) :
    subPoly P ((clipList l p).rotate 1) = clip (subPoly P l) p := by
  have hlen := length_clipList l p (by omega)
  have hn := n_subPoly P l
  apply polygon_ext
  rw [vertices_subPoly]
  unfold clip Polygon.arc
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_map, List.getElem?_map]
  by_cases hk : k < l.length - 1
  · rw [List.getElem?_range (by omega), List.getElem?_rotate (by omega), hlen,
      getElem?_clipList l p (by omega) (Nat.mod_lt _ (by omega)), Option.map_some,
      prevIdx_add_two_add_mod _ (by rw [hn]; exact hp), hn,
      vtx_subPoly P l (Nat.mod_lt _ (by omega))]
    by_cases hk1 : k + 1 < l.length - 1
    · rw [ite_eq_right (by rw [Nat.mod_eq_of_lt hk1]; omega), Nat.mod_eq_of_lt hk1,
        List.getElem?_eq_getElem (Nat.mod_lt _ (by omega)), Option.map_some,
        show p + (k + 1) = p + 1 + k by omega]
    · have hk1' : k + 1 = l.length - 1 := by omega
      rw [hk1', Nat.mod_self, ite_eq_left rfl, List.getElem?_eq_getElem (Nat.mod_lt _ (by omega)),
        Option.map_some, show p + 1 + k = p + l.length - 1 by omega]
  · rw [List.getElem?_eq_none (by rw [List.length_rotate, hlen]; omega),
      List.getElem?_eq_none (by rw [List.length_range]; omega)]
    rfl

/-- The sub-polygon of the clipped list is the clipped polygon rotated by `m - 2`. -/
theorem subPoly_clipList_eq (l : List ℕ) (p : ℕ) (h3 : 3 ≤ l.length) (hp : p < l.length) :
    subPoly P (clipList l p) = (clip (subPoly P l) p).rotate (l.length - 2) := by
  rw [← subPoly_clipList_rotate P l p h3 hp, ← subPoly_rotate, List.rotate_rotate]
  congr 1
  rw [show 1 + (l.length - 2) = (clipList l p).length by rw [length_clipList l p (by omega)]; omega,
    List.rotate_length]

/-! ### Relabelling triangles -/

/-- A triangle given by positions in `l`, mapped to original indices. -/
def relabelList (l : List ℕ) (t : Polygon.Triangle) : Polygon.Triangle :=
  (l.getD t.1 0, l.getD t.2.1 0, l.getD t.2.2 0)

/-- Relabelling through `List.range n` is the identity on triangles with indices `< n`. -/
theorem relabelList_range {n : ℕ} {t : Polygon.Triangle} (h : t.1 < n ∧ t.2.1 < n ∧ t.2.2 < n) :
    relabelList (List.range n) t = t := by
  obtain ⟨t1, t2, t3⟩ := t
  simp only [relabelList]
  rw [getD_range h.1, getD_range h.2.1, getD_range h.2.2]

/-- The position map from `clipList l p` (length `m - 1`) to `l` (length `m`), as a triangle
relabelling: rotate by `m - 2` (undoing the rotation of `subPoly_clipList_eq`) then embed the
clipped polygon `clip (subPoly P l) p` into `subPoly P l` via `i ↦ (p + 1 + i) % m`. -/
def clipRelabel (m p : ℕ) (t : Polygon.Triangle) : Polygon.Triangle :=
  relabel ((p + 1) % m) m (relabel (m - 2) (m - 1) t)

/-- The scalar version of `clipRelabel` agrees with the entries of `clipList`. -/
theorem getD_clipList_eq (l : List ℕ) (p : ℕ) (h3 : 3 ≤ l.length) {i : ℕ}
    (hi : i < l.length - 1) :
    (clipList l p).getD i 0 =
      l.getD (((p + 1) % l.length + (l.length - 2 + i) % (l.length - 1)) % l.length) 0 := by
  rw [getD_clipList l p (by omega) hi]
  split_ifs with h0
  · subst h0
    rw [Nat.mod_eq_of_lt (by omega : l.length - 2 + 0 < l.length - 1),
      Nat.mod_add_mod, show p + 1 + (l.length - 2 + 0) = p + l.length - 1 by omega]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [show l.length - 2 + (k + 1) = k + (l.length - 1) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : k < l.length - 1), Nat.mod_add_mod,
      show p + 1 + k = p + (k + 1) by omega]

/-- Relabelling a triangle of `clipList l p` to original indices, through `clipRelabel`. -/
theorem relabelList_clipRelabel (l : List ℕ) (p : ℕ) (h3 : 3 ≤ l.length) {t : Polygon.Triangle}
    (ht : t.1 < l.length - 1 ∧ t.2.1 < l.length - 1 ∧ t.2.2 < l.length - 1) :
    relabelList l (clipRelabel l.length p t) = relabelList (clipList l p) t := by
  obtain ⟨t1, t2, t3⟩ := t
  simp only [relabelList, clipRelabel, relabel_fst, relabel_snd_fst, relabel_snd_snd]
  rw [getD_clipList_eq l p h3 ht.1, getD_clipList_eq l p h3 ht.2.1, getD_clipList_eq l p h3 ht.2.2]

/-! ### Weak triangulations and rotation -/

/-- **Weak triangulations transfer along rotation**: a weak triangulation of `P.rotate s`
relabels (`relabel s P.n`) to a weak triangulation of `P`. -/
theorem weakTriangulates_rotate (s : ℕ) {T : List Polygon.Triangle}
    (hT : WeakTriangulates (P.rotate s) T) : WeakTriangulates P (T.map (relabel s P.n)) := by
  obtain ⟨hvalid, hcount, hunion, hdisj, hvert⟩ := hT
  have hidx : ∀ t ∈ T, t.1 < P.n ∧ t.2.1 < P.n ∧ t.2.2 < P.n := by
    intro t ht
    obtain ⟨h1, h2, h3, -⟩ := hvalid t ht
    rw [n_rotate] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [List.mem_map] at ht
    obtain ⟨t', ht', rfl⟩ := ht
    exact validTriangle_rotate P s (hvalid t' ht')
  · rw [List.length_map, ← n_rotate P s]; exact hcount
  · rw [← filled_rotate P s, ← hunion]
    ext p
    simp only [Set.mem_ofPred_eq, List.mem_map]
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, hp⟩
      exact ⟨t, ht, by rw [triSet_rotate P s (hidx t ht)]; exact hp⟩
    · rintro ⟨t, ht, hp⟩
      exact ⟨_, ⟨t, ht, rfl⟩, by rw [← triSet_rotate P s (hidx t ht)]; exact hp⟩
  · rw [List.pairwise_map]
    refine hdisj.imp_of_mem ?_
    intro a b ha hb h
    rw [triSet_rotate P s (hidx a ha), triSet_rotate P s (hidx b hb)] at h
    exact h
  · intro t ht i hi hmem
    rw [List.mem_map] at ht
    obtain ⟨t', ht', rfl⟩ := ht
    obtain ⟨j, hj, hji⟩ := exists_rot_index (by omega) s i hi
    have e1 : P.vtx i = (P.rotate s).vtx j := by rw [vtx_rotate P s hj, hji]
    rw [e1, ← triSet_rotate P s (hidx t' ht')] at hmem
    rw [e1, ← triVertices_rotate P s (hidx t' ht')]
    exact hvert t' ht' j (by rw [n_rotate]; exact hj) hmem

/-! ### The clipping step for sub-polygons -/

/-- **Ear clipping on index lists.**  If position `p` of `l` is an ear of `Q = subPoly P l`
and `T` weakly triangulates `subPoly P (clipList l p)` (triangles in positions of
`clipList l p`), then `earTriangle Q p :: T.map (clipRelabel m p)` weakly triangulates `Q`
(triangles in positions of `l`). -/
theorem weakTriangulates_clipList (l : List ℕ) (p : ℕ) (h3 : 3 ≤ l.length) (hp : p < l.length)
    (hQ : (subPoly P l).Simple) (he : IsEar (subPoly P l) p) {T : List Polygon.Triangle}
    (hT : WeakTriangulates (subPoly P (clipList l p)) T) :
    WeakTriangulates (subPoly P l)
      (earTriangle (subPoly P l) p :: T.map (clipRelabel l.length p)) := by
  have hn := n_subPoly P l
  have hp' : p < (subPoly P l).n := by rw [hn]; exact hp
  rw [subPoly_clipList_eq P l p h3 hp] at hT
  have h1 := weakTriangulates_rotate _ _ hT
  rw [n_clip _ _ (by rw [hn]; omega), hn] at h1
  have h2 := weakTriangulates_clip _ _ hQ hp' he h1
  rw [List.map_map, prevIdx_add_two_mod _ hp', hn] at h2
  exact h2

/-- Simplicity of the sub-polygon of the clipped list. -/
theorem simple_subPoly_clipList (l : List ℕ) (p : ℕ) (h3 : 3 ≤ l.length) (hp : p < l.length)
    (hQ : (subPoly P l).Simple) (he : IsEar (subPoly P l) p) :
    (subPoly P (clipList l p)).Simple := by
  rw [subPoly_clipList_eq P l p h3 hp]
  exact simple_rotate _ _ (simple_clip _ _ hQ he)

end

end Chazelle.EarClip
