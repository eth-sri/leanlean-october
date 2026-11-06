module

public import Chazelle.Mountain.PiecesMain
public import Chazelle.Split.Multi
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics
public import Chazelle.ChainTactics

/-!
# Triangulating one piece: the abstract algorithm

A *piece* of the subdivision (`Chazelle.Mountain.IsPiece`) is handed to the final stage as a
cyclic list `l` of vertex indices (in the RAM, a cyclic linked list; see `RamPieceTri.lean`).
By the mountain decomposition theorem (`Chazelle.Mountain.piece_isMountain`) it is a monotone
mountain after a rotation, possibly after reversal:
`∃ s, IsMountain ((subPoly P l).rotate s) ∨ IsMountain ((subPoly P l.reverse).rotate s)`.

The linear-time reorientation implemented on the RAM:

1. find a position `i0` of a `ylexLT`-minimal vertex (`IsMinPos`, a single scan);
2. compare the two cyclic neighbours of the minimum: the chain is increasing *forward* from the
   minimum iff the successor is `ylexLT`-below the predecessor (`DirFwd`) — in a mountain one
   neighbour of the minimum is the maximum (the base joins them), and the other is not;
3. read the list from `i0` forward (`fwdList l i0`) or backward (`bwdList l i0`):
   `reorient P l i0`.

## Main results

* `exists_isMinPos`, `isMinPos_unique`: a minimum position exists, and it is unique on a piece
  whose vertex list is a rotated (possibly reversed) mountain.
* `mountain_case_rotate`, `mountain_case_reverse`: direction choice correctness in the two
  cases of the mountain theorem.
* `isMountain_reorient`: `IsMountain (subPoly P (reorient P l i0))`.
* `weakTriangulates_subPoly_reverse`, `goodTri_of_reverse`, `goodTri_of_rotate`,
  `goodTri_of_reorient`: a relabelled weak triangulation of the reoriented list is one of `l`
  (`GoodTri P l T`, i.e. `T = T'.map (relabelList l)` with `WeakTriangulates (subPoly P l) T'`).
* `goodTri_piece_of_mountain`: the composed abstract statement used by the RAM proof.
* `triangulates_of_goodTri_pieces`: if every piece `m` of `splitAll (List.range P.n) D`
  (`D` an `EnumDiags P D`) gets an output `O m` with `GoodTri P m (O m)` (the form produced by
  `pieceTri_exec`), the concatenation `(splitAll …).flatMap O` triangulates `P`.
-/

namespace Chazelle.Final

@[expose] public section

open Chazelle.Mountain
open Chazelle.EarClip (subPoly n_subPoly vtx_subPoly_getD relabelList subPoly_rotate
  getD_eq_getElem_of_lt getD_rotate)
open Chazelle.Existence (WeakTriangulates)

/-! ### Definitions -/

/-- The point at position `i` of the index list `l`. -/
noncomputable def ptAt (P : Polygon) (l : List ℕ) (i : ℕ) : Point := P.vtx (l.getD i 0)

/-- Position `i0` holds a `ylexLT`-minimal vertex of `l` (no vertex is strictly below it). -/
def IsMinPos (P : Polygon) (l : List ℕ) (i0 : ℕ) : Prop :=
  i0 < l.length ∧ ∀ j, j < l.length → ¬ ylexLT (ptAt P l j) (ptAt P l i0)

/-- The list read forward from position `i0`: entry `j` is `l[(i0 + j) % m]`. -/
def fwdList (l : List ℕ) (i0 : ℕ) : List ℕ :=
  (List.range l.length).map (fun j => l.getD ((i0 + j) % l.length) 0)

/-- The list read backward from position `i0`: entry `j` is `l[(i0 + m - j) % m]`. -/
def bwdList (l : List ℕ) (i0 : ℕ) : List ℕ :=
  (List.range l.length).map (fun j => l.getD ((i0 + l.length - j) % l.length) 0)

/-- The direction test: the successor of position `i0` is `ylexLT`-below its predecessor. -/
def DirFwd (P : Polygon) (l : List ℕ) (i0 : ℕ) : Prop :=
  ylexLT (ptAt P l ((i0 + 1) % l.length)) (ptAt P l ((i0 + l.length - 1) % l.length))

open Classical in
/-- **The reoriented list**: forward from `i0` if `DirFwd`, backward otherwise. -/
noncomputable def reorient (P : Polygon) (l : List ℕ) (i0 : ℕ) : List ℕ :=
  if DirFwd P l i0 then fwdList l i0 else bwdList l i0

/-! ### Elementary list and index facts -/

theorem length_fwdList (l : List ℕ) (i0 : ℕ) : (fwdList l i0).length = l.length := by
  simp [fwdList]

theorem length_bwdList (l : List ℕ) (i0 : ℕ) : (bwdList l i0).length = l.length := by
  simp [bwdList]

theorem getD_fwdList (l : List ℕ) (i0 : ℕ) {j : ℕ} (hj : j < l.length) :
    (fwdList l i0).getD j 0 = l.getD ((i0 + j) % l.length) 0 := by
  simp [fwdList, List.getD_eq_getElem?_getD, hj]

theorem getD_bwdList (l : List ℕ) (i0 : ℕ) {j : ℕ} (hj : j < l.length) :
    (bwdList l i0).getD j 0 = l.getD ((i0 + l.length - j) % l.length) 0 := by
  simp [bwdList, List.getD_eq_getElem?_getD, hj]

theorem length_reorient (P : Polygon) (l : List ℕ) (i0 : ℕ) :
    (reorient P l i0).length = l.length := by
  unfold reorient; split_ifs
  · exact length_fwdList l i0
  · exact length_bwdList l i0

/-- Two lists of the same length with the same `getD` entries are equal. -/
theorem list_eq_of_getD {l₁ l₂ : List ℕ} (hlen : l₁.length = l₂.length)
    (h : ∀ i, i < l₁.length → l₁.getD i 0 = l₂.getD i 0) : l₁ = l₂ := by
  apply List.ext_getElem hlen
  intro i h1 h2
  have := h i h1
  rwa [getD_eq_getElem_of_lt _ _ h1, getD_eq_getElem_of_lt _ _ h2] at this

/-- Reduction of `a % m` for `a < 2 m`. -/
theorem mod_of_lt_two_mul {a m : ℕ} (h : a < 2 * m) : a % m = if a < m then a else a - m := by
  split_ifs with h'
  · exact Nat.mod_eq_of_lt h'
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Every residue `x < m` is `(j + r) % m` for some `j < m`, with `j = 0` iff `x = r`. -/
theorem exists_add_mod_eq {m r x : ℕ} (hr : r < m) (hx : x < m) :
    ∃ j, j < m ∧ (j + r) % m = x ∧ (j = 0 ↔ x = r) := by
  by_cases h : r ≤ x
  · refine ⟨x - r, by omega, ?_, by omega⟩
    rwo [Nat.mod_eq_of_lt (by omega)]
  · refine ⟨x + m - r, by omega, ?_, by omega⟩
    rwo [mod_of_lt_two_mul (by omega), ite_eq_right (by omega)]

/-- The forward list from `i0` is the rotation by `i0`. -/
theorem fwdList_eq_rotate (l : List ℕ) (i0 : ℕ) : fwdList l i0 = l.rotate i0 := by
  apply list_eq_of_getD (by rw [length_fwdList, List.length_rotate])
  intro j hj
  rw [length_fwdList] at hj
  rw [getD_fwdList l i0 hj, getD_rotate l i0 j hj, Nat.add_comm]

/-- The backward list from `i0 < m` is the reversal rotated by `m - 1 - i0`. -/
theorem bwdList_eq_reverse_rotate {l : List ℕ} {i0 : ℕ} (hi0 : i0 < l.length) :
    bwdList l i0 = l.reverse.rotate (l.length - 1 - i0) := by
  apply list_eq_of_getD (by rw [length_bwdList, List.length_rotate, List.length_reverse])
  intro j hj
  rw [length_bwdList] at hj
  rw [getD_bwdList l i0 hj,
    getD_rotate l.reverse _ j (by rwx [List.length_reverse]), List.length_reverse,
    getD_reverse l (Nat.mod_lt _ (by omega))]
  congr 1
  rw [mod_of_lt_two_mul (a := i0 + l.length - j) (by omega),
    mod_of_lt_two_mul (a := j + (l.length - 1 - i0)) (by omega)]
  splao

/-! ### Transfer of weak triangulations -/

/-- Reversing the positions of a triangle in a list of length `m`. -/
def revTri (m : ℕ) (t : Polygon.Triangle) : Polygon.Triangle :=
  (m - 1 - t.1, m - 1 - t.2.1, m - 1 - t.2.2)

section transfer
variable (P : Polygon)

/-- The triangle `revTri m t` of `subPoly P l` has the vertices of `t` in `subPoly P l.reverse`. -/
theorem triVertices_revTri {l : List ℕ} {t : Polygon.Triangle}
    (h : t.1 < l.length ∧ t.2.1 < l.length ∧ t.2.2 < l.length) :
    (subPoly P l).triVertices (revTri l.length t) = (subPoly P l.reverse).triVertices t := by
  unfold Polygon.triVertices revTri
  rw [vtx_subPoly_reverse P l h.1, vtx_subPoly_reverse P l h.2.1, vtx_subPoly_reverse P l h.2.2]

theorem triSet_revTri {l : List ℕ} {t : Polygon.Triangle}
    (h : t.1 < l.length ∧ t.2.1 < l.length ∧ t.2.2 < l.length) :
    (subPoly P l).triSet (revTri l.length t) = (subPoly P l.reverse).triSet t := by
  unfold Polygon.triSet
  rw [triVertices_revTri P h]

/-- **Weak triangulations transfer along reversal**: a weak triangulation of
`subPoly P l.reverse` gives one of `subPoly P l` by reversing positions (`revTri`). -/
theorem weakTriangulates_subPoly_reverse {l : List ℕ} {T : List Polygon.Triangle}
    (hT : WeakTriangulates (subPoly P l.reverse) T) :
    WeakTriangulates (subPoly P l) (T.map (revTri l.length)) := by
  obtain ⟨hvalid, hcount, hunion, hdisj, hvert⟩ := hT
  have hidx : ∀ t ∈ T, t.1 < l.length ∧ t.2.1 < l.length ∧ t.2.2 < l.length := by
    intro t ht
    obtain ⟨h1, h2, h3, -⟩ := hvalid t ht
    rw [n_subPoly, List.length_reverse] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [List.mem_map] at ht
    obtain ⟨t', ht', rfl⟩ := ht
    obtain ⟨h1, h2, h3⟩ := hidx t' ht'
    obtain ⟨-, -, -, hdet⟩ := hvalid t' ht'
    refine ⟨by rsio [n_subPoly] only [revTri],
      by rsio [n_subPoly] only [revTri],
      by rsio [n_subPoly] only [revTri], ?_⟩
    unfold revTri
    rw [← vtx_subPoly_reverse P l h1, ← vtx_subPoly_reverse P l h2,
      ← vtx_subPoly_reverse P l h3]
    exact hdet
  · rw [n_subPoly, List.length_reverse] at hcount
    rw [List.length_map, n_subPoly]
    exact hcount
  · rw [← filled_subPoly_reverse P l, ← hunion]
    ext p
    simp only [Set.mem_ofPred_eq, List.mem_map]
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, hp⟩
      exact ⟨t, ht, by rwx [← triSet_revTri P (hidx t ht)]⟩
    · rintro ⟨t, ht, hp⟩
      exact ⟨_, ⟨t, ht, rfl⟩, by rwx [triSet_revTri P (hidx t ht)]⟩
  · rw [List.pairwise_map]
    refine hdisj.imp_of_mem ?_
    intro a b ha hb h
    rw [triSet_revTri P (hidx a ha), triSet_revTri P (hidx b hb)]
    exact h
  · intro t ht i hi hmem
    rw [List.mem_map] at ht
    obtain ⟨t', ht', rfl⟩ := ht
    rw [n_subPoly] at hi
    have e : (subPoly P l).vtx i = (subPoly P l.reverse).vtx (l.length - 1 - i) := by
      rw [vtx_subPoly_reverse P l (by omega)]; congr 1; omega
    rw [e, triSet_revTri P (hidx t' ht')] at hmem
    rw [e, triVertices_revTri P (hidx t' ht')]
    exact hvert t' ht' _ (by rwo [n_subPoly, List.length_reverse]) hmem

/-- **Relabelled weak triangulations transfer along reversal of the index list.** -/
theorem goodTri_of_reverse {l : List ℕ} {T : List Polygon.Triangle}
    (h : GoodTri P l.reverse T) : GoodTri P l T := by
  obtain ⟨T', hT', rfl⟩ := h
  refine ⟨_, weakTriangulates_subPoly_reverse P hT', ?_⟩
  rw [List.map_map]
  apply List.map_congr_left
  intro t ht
  obtain ⟨h1, h2, h3, -⟩ := hT'.1 t ht
  rw [n_subPoly, List.length_reverse] at h1 h2 h3
  obtain ⟨a, b, d⟩ := t
  simp only [Function.comp, relabelList, revTri]
  rw [getD_reverse l h1, getD_reverse l h2, getD_reverse l h3]

/-- **Relabelled weak triangulations transfer back along rotation of the index list.** -/
theorem goodTri_of_rotate {l : List ℕ} {r : ℕ} {T : List Polygon.Triangle}
    (h : GoodTri P (l.rotate r) T) : GoodTri P l T := by
  have := goodTri_rotate P h (l.length - r % l.length)
  rwa [rotate_rotate_cancel] at this

/-- **Transfer for the reoriented list**: a relabelled weak triangulation of
`reorient P l i0` (`i0 < m`) is a relabelled weak triangulation of `l`. -/
theorem goodTri_of_reorient {l : List ℕ} {i0 : ℕ} (hi0 : i0 < l.length)
    {T : List Polygon.Triangle} (h : GoodTri P (reorient P l i0) T) : GoodTri P l T := by
  unfold reorient at h
  split_ifs at h
  · rw [fwdList_eq_rotate] at h
    exact goodTri_of_rotate P h
  · rw [bwdList_eq_reverse_rotate hi0] at h
    exact goodTri_of_reverse P (goodTri_of_rotate P h)

end transfer

/-! ### The minimum -/

section minimum
variable {P : Polygon} {l : List ℕ}

/-- **Case 1 of the mountain theorem** (the list rotated by `r` is a mountain): the minimum
position is `r`, the direction test is positive, and the forward list is that mountain list. -/
theorem mountain_case_rotate {r i0 : ℕ} (hr : r < l.length)
    (hM : IsMountain (subPoly P (l.rotate r))) (hmin : IsMinPos P l i0) :
    i0 = r ∧ DirFwd P l i0 ∧ fwdList l i0 = l.rotate r := by
  set m := l.length with hm
  have hn : (subPoly P (l.rotate r)).n = m := by rw [n_subPoly, List.length_rotate]
  have h3 : 3 ≤ m := by have := hM.1.1; omega
  have hv : ∀ j, j < m → (subPoly P (l.rotate r)).vtx j = ptAt P l ((j + r) % m) := by
    intro j hj
    rw [vtx_subPoly_getD P _ (by rwx [List.length_rotate]), getD_rotate l r j hj]
    rfl
  have hi0 : i0 = r := by
    by_contra hne
    obtain ⟨j, hj, hjr, hj0⟩ := exists_add_mod_eq hr hmin.1
    have hjpos : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · exact absurd (hj0.1 h) hne
      · exact h
    have := ylexLT_of_lt _ hM hjpos (by rwx [hn])
    rw [hv 0 (by omega), hv j hj, hjr, Nat.zero_add, Nat.mod_eq_of_lt hr] at this
    exact hmin.2 r hr this
  subst hi0
  refine ⟨rfl, ?_, fwdList_eq_rotate l _⟩
  have := ylexLT_of_lt _ hM (i := 1) (j := m - 1) (by omega) (by rwo [hn])
  rw [hv 1 (by omega), hv (m - 1) (by omega)] at this
  unfold DirFwd
  rw [← hm, Nat.add_comm i0 1, show i0 + m - 1 = m - 1 + i0 by omega]
  exact this

/-- **Case 2 of the mountain theorem** (the reversed list rotated by `r` is a mountain): the
minimum position is `m - 1 - r`, the direction test is negative, and the backward list is that
mountain list. -/
theorem mountain_case_reverse {r i0 : ℕ} (hr : r < l.length)
    (hM : IsMountain (subPoly P (l.reverse.rotate r))) (hmin : IsMinPos P l i0) :
    i0 = l.length - 1 - r ∧ ¬ DirFwd P l i0 ∧ bwdList l i0 = l.reverse.rotate r := by
  set m := l.length with hm
  have hn : (subPoly P (l.reverse.rotate r)).n = m := by
    rw [n_subPoly, List.length_rotate, List.length_reverse]
  have h3 : 3 ≤ m := by have := hM.1.1; omega
  have hv : ∀ j, j < m →
      (subPoly P (l.reverse.rotate r)).vtx j = ptAt P l (m - 1 - (j + r) % m) := by
    intro j hj
    rw [vtx_subPoly_getD P _ (by rwx [List.length_rotate, List.length_reverse]),
      getD_rotate l.reverse r j (by rwx [List.length_reverse]), List.length_reverse,
      getD_reverse l (Nat.mod_lt _ (by omega))]
    rfl
  have hi0m  := hmin.1
  have hi0 : i0 = m - 1 - r := by
    by_contra hne
    obtain ⟨j, hj, hjr, hj0⟩ := exists_add_mod_eq (x := m - 1 - i0) hr (by omega)
    have hjpos : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · exact absurd (hj0.1 h) (by omega)
      · exact h
    have := ylexLT_of_lt _ hM hjpos (by rwx [hn])
    rw [hv 0 (by omega), hv j hj, hjr, Nat.zero_add, Nat.mod_eq_of_lt hr,
      show m - 1 - (m - 1 - i0) = i0 by have := hmin.1; omega] at this
    exact hmin.2 _ (by omega) this
  subst hi0
  refine ⟨rfl, ?_, ?_⟩
  · have := ylexLT_of_lt _ hM (i := 1) (j := m - 1) (by omega) (by rwo [hn])
    rw [hv 1 (by omega), hv (m - 1) (by omega)] at this
    intro hd
    unfold DirFwd at hd
    rw [← hm] at hd
    have e1 : (m - 1 - r + 1) % m = m - 1 - (m - 1 + r) % m := by
      rw [mod_of_lt_two_mul (a := m - 1 - r + 1) (by omega),
        mod_of_lt_two_mul (a := m - 1 + r) (by omega)]
      splao
    have e2 : (m - 1 - r + m - 1) % m = m - 1 - (1 + r) % m := by
      rw [mod_of_lt_two_mul (a := m - 1 - r + m - 1) (by omega),
        mod_of_lt_two_mul (a := 1 + r) (by omega)]
      splao
    rw [e1, e2] at hd
    exact ylexLT_asymm this hd
  · rw [bwdList_eq_reverse_rotate (by omega), ← hm]
    congr 1
    omega

/-- The two cases of the mountain theorem, with the rotation reduced below `m`. -/
theorem mountain_cases (hmount : ∃ s, IsMountain ((subPoly P l).rotate s) ∨
      IsMountain ((subPoly P l.reverse).rotate s)) (h0 : 0 < l.length) :
    ∃ r, r < l.length ∧
      (IsMountain (subPoly P (l.rotate r)) ∨ IsMountain (subPoly P (l.reverse.rotate r))) := by
  obtain ⟨s, h | h⟩ := hmount
  · refine ⟨s % l.length, Nat.mod_lt _ h0, Or.inl ?_⟩
    rwx [List.rotate_mod, subPoly_rotate]
  · refine ⟨s % l.length, Nat.mod_lt _ h0, Or.inr ?_⟩
    have e : l.reverse.rotate (s % l.length) = l.reverse.rotate s := by
      rw [← List.length_reverse (as := l), List.rotate_mod]
    rwx [e, subPoly_rotate]

/-- **The reoriented list is a monotone mountain**: from any minimum position `i0` of a piece
whose vertex list is a rotated (possibly reversed) mountain, `reorient P l i0` lists the piece
in strictly increasing `ylexLT` order. -/
theorem isMountain_reorient (hmount : ∃ s, IsMountain ((subPoly P l).rotate s) ∨
      IsMountain ((subPoly P l.reverse).rotate s)) {i0 : ℕ} (hmin : IsMinPos P l i0) :
    IsMountain (subPoly P (reorient P l i0)) := by
  obtain ⟨r, hr, hM | hM⟩ := mountain_cases hmount (by have := hmin.1; omega)
  · obtain ⟨-, hd, he⟩ := mountain_case_rotate hr hM hmin
    unfold reorient
    rw [ite_eq_left hd, he]
    exact hM
  · obtain ⟨-, hd, he⟩ := mountain_case_reverse hr hM hmin
    unfold reorient
    rw [ite_eq_right hd, he]
    exact hM

/-- **The abstract piece triangulator**: on a piece given as a rotated (possibly reversed)
mountain, with `i0` a minimum position, any relabelled weak triangulation of the reoriented
mountain `reorient P l i0` is a relabelled weak triangulation of the piece. -/
theorem goodTri_piece_of_mountain {i0 : ℕ} (hmin : IsMinPos P l i0)
    {T : List Polygon.Triangle} (h : GoodTri P (reorient P l i0) T) : GoodTri P l T :=
  goodTri_of_reorient P hmin.1 h

end minimum

/-! ### Composition over all pieces -/

end

end Chazelle.Final
